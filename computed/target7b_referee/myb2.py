"""Referee (target 7b): own exact check  B2(N) >= V ?  (independent of b2fast and tworise)

r = 2 form of Theorem 1: alpha(k0,l0) = -1 + u_k0 (1 - 2^l0), u_k = (2/3)^k = 2^k v_k, v_k = 3^-k;
B2(N) = max{ z_N(alpha) - l0 : z_N(alpha) > k0 + l0 }.
 * k0 = N: n = 2^N - 1, simulated literally.
 * k0 <= KS (small, periodic windows): exhaustive over l0 <= Lam(k0), where for an actual n < 2^N
   n1 + 1 < 3^k0 2^(N-k0-l0) + 1 and n1 + 1 >= 2^k1 >= 2^(V-k0), so 2^(V-k0) - 1 < 3^k0 2^(N-k0-l0);
   each candidate evaluated exactly (gmpy2).
 * KS < k0 < N, k0 + l0 >= N ('region C'): l0 forced = z_N(u_k0) - k0 (bit N.. of u-1 = of u),
   value = k0 + v2((v >> l0) - v)  (64-bit window, exact fallback if 0).
 * KS < k0, k0 + l0 < N: value >= V  <=>  bits [N, V + l0) of alpha zero;
   alpha >> N = (u >> N) - (u >> (N - l0)) - b,  b in {0,1} not computed (both tried):
   win(v, N-k0) - win(v, N-k0-l0) - b = 0 mod 2^min(64, t+l0).  Matches evaluated exactly.
v_k is advanced by exact 2-adic division by 3 on a limb array (numba).
"""
import sys, os, time, math, json
import numpy as np
import numba as nb
from numba import njit, prange
import gmpy2
from gmpy2 import mpz
from fractions import Fraction as F

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)
INV3 = U64(0xAAAAAAAAAAAAAAAB)       # 3 * INV3 = 1 mod 2^64
assert (3 * 0xAAAAAAAAAAAAAAAB) % (1 << 64) == 1


@njit
def div3(v):
    """v <- v / 3 (2-adic, exact mod 2^(64 len))"""
    c = U64(0)
    for i in range(v.shape[0]):
        a = v[i]
        bor = U64(1) if a < c else U64(0)
        tt = a - c
        q = tt * INV3
        # h = floor(3 q / 2^64)
        q2 = q << U64(1)
        h = q >> U64(63)
        s = q2 + q
        if s < q2:
            h += U64(1)
        v[i] = q
        c = h + bor


@njit(inline='always')
def win(v, pos):
    if pos >= 0:
        w = pos >> 6
        s = pos & 63
        lo = v[w] >> U64(s)
        if s != 0:
            lo |= v[w + 1] << U64(64 - s)
        return lo
    if pos <= -64:
        return U64(0)
    return v[0] << U64(-pos)


@njit(inline='always')
def lowmask(w):
    if w >= 64:
        return ALL
    return (U64(1) << U64(w)) - U64(1)


@njit(parallel=True)
def scan(v, N, t, KS, out, cnt, cout, ccnt):
    """region A matches -> out; region C values -> cout (k0, value) where value >= N + t or fallback"""
    k0 = 0
    for k in range(1, N):
        div3(v)
        k0 = k
        if k0 <= KS:
            continue
        D0 = N - k0
        # region C: l0 = (lowest set bit of v at index >= D0) - 0 ... in u coordinates
        # z_N(u) = k0 + first set bit of v at >= D0
        p = D0
        found = -1
        while p + 128 < v.shape[0] * 64:
            x = win(v, p)
            if x != U64(0):
                b = 0
                while (x >> U64(b)) & U64(1) == U64(0):
                    b += 1
                found = p + b
                break
            p += 64
        c = ccnt[0]
        if found < 0:
            if c < cout.shape[0]:
                cout[c, 0] = k0; cout[c, 1] = -1
            ccnt[0] = c + 1
        else:
            l0 = found               # z_N(u) - k0
            dd = win(v, l0) - win(v, 0)
            if dd == U64(0):
                if c < cout.shape[0]:
                    cout[c, 0] = k0; cout[c, 1] = -2
                ccnt[0] = c + 1
            else:
                g = 0
                while (dd >> U64(g)) & U64(1) == U64(0):
                    g += 1
                val = k0 + g
                if val >= N + t:
                    if c < cout.shape[0]:
                        cout[c, 0] = k0; cout[c, 1] = val
                    ccnt[0] = c + 1
        # region A, parallel over l0
        x0 = win(v, D0)
        L = D0 - 1
        nch = 64
        step = (L + nch - 1) // nch
        for ch in prange(nch):
            th = nb.get_thread_id()
            a = 1 + ch * step
            b_ = min(L, a + step - 1)
            for l0 in range(a, b_ + 1):
                d = x0 - win(v, D0 - l0)
                m = lowmask(t + l0)
                if (d & m) == U64(0) or ((d - U64(1)) & m) == U64(0):
                    cc = cnt[th]
                    if cc < out.shape[1]:
                        out[th, cc, 0] = k0
                        out[th, cc, 1] = l0
                    cnt[th] = cc + 1


def runs2(n):
    n = mpz(n)
    k0 = gmpy2.bit_scan0(n)
    x = ((n + 1) >> k0) * mpz(3) ** k0 - 1
    l0 = gmpy2.bit_scan1(x)
    x >>= l0
    k1 = gmpy2.bit_scan0(x)
    return k0, l0, k1


def alpha_exact(N, k0, l0):
    """(z_N(alpha), value, valid)"""
    R = N + l0 + 256
    while True:
        mod = mpz(1) << R
        u = (pow(mpz(3), -k0, mod) << k0) % mod
        al = (-1 + u * (1 - (mpz(1) << l0))) % mod
        y = al >> N
        if y != 0:
            z = N + gmpy2.bit_scan1(y)
            return z, z - l0, z > k0 + l0
        R *= 2


def check(N, V, nthreads=4, KSmax=30, verbose=True):
    """every (k0, l0, value) with value >= V; returns (best, hits, stats)"""
    T0 = time.time()
    t = V - N
    assert t >= 1
    hits = []
    # k0 = N
    n = (mpz(1) << N) - 1
    r = runs2(n)
    assert r[0] == N
    if r[0] + r[2] >= V:
        hits.append(((N, r[1]), r[0] + r[2]))
    # small k0: exhaustive with rigorous l0 bound
    KS = 0
    nsmall = 0
    for k0 in range(1, min(KSmax, N - 1) + 1):
        lhs = mpz(2) ** (V - k0) - 1
        if lhs <= 0:
            break
        lam = 0          # largest l0 with 3^k0 2^(N-k0-l0) > lhs
        while F(3) ** k0 * F(2) ** (N - k0 - (lam + 1)) > lhs:
            lam += 1
        for l0 in range(1, lam + 1):
            nsmall += 1
            z, val, ok = alpha_exact(N, k0, l0)
            if ok and val >= V:
                hits.append(((k0, l0), val))
        KS = k0
    M = ((N + 256) // 64 + 2) * 64
    v = np.zeros(M // 64, dtype=np.uint64)
    v[0] = U64(1)
    nb.set_num_threads(nthreads)
    NT = nb.config.NUMBA_NUM_THREADS
    out = np.zeros((NT, 1 << 16, 2), dtype=np.int64)
    cnt = np.zeros(NT, dtype=np.int64)
    cout = np.zeros((1 << 16, 2), dtype=np.int64)
    ccnt = np.zeros(1, dtype=np.int64)
    scan(v, N, t, KS, out, cnt, cout, ccnt)
    assert (cnt <= out.shape[1]).all() and ccnt[0] <= cout.shape[0], "overflow"
    # check the final v equals 3^-(N-1) mod 2^M (end-to-end test of the division)
    vref = pow(mpz(3), -(N - 1), mpz(1) << M)
    assert int.from_bytes(v.tobytes(), 'little') == int(vref), "div3 mismatch"
    nA = int(cnt.sum())
    for th in range(NT):
        for i in range(cnt[th]):
            k0, l0 = int(out[th, i, 0]), int(out[th, i, 1])
            z, val, ok = alpha_exact(N, k0, l0)
            if ok and val >= V:
                hits.append(((k0, l0), val))
    nC = int(ccnt[0])
    for i in range(nC):
        k0, val = int(cout[i, 0]), int(cout[i, 1])
        if val < 0:        # fallback: exact region-C evaluation via the forced l0
            R = 2 * N + 512
            mod = mpz(1) << R
            u = (pow(mpz(3), -k0, mod) << k0) % mod
            l0 = N + gmpy2.bit_scan1(u >> N) - k0
            z, val, ok = alpha_exact(N, k0, l0)
            if ok and val >= V:
                hits.append(((k0, l0), val))
        else:
            hits.append(((k0, -1), val))
    best = max([h[1] for h in hits], default=None)
    st = dict(N=N, V=V, KS=KS, nsmall=nsmall, nA=nA, nC=nC, secs=round(time.time() - T0, 1))
    return best, hits, st


def witness(N, k0, l0):
    """rebuild n < 2^N and simulate"""
    if l0 == -1:   # region C: n = (u_k0 - 1) mod 2^N
        u = (pow(mpz(3), -k0, mpz(1) << N) << k0) % (mpz(1) << N)
        n = (u - 1) % (mpz(1) << N)
    elif k0 == N:
        n = (mpz(1) << N) - 1
    else:
        mod = mpz(1) << (N + l0 + 256)
        u = (pow(mpz(3), -k0, mod) << k0) % mod
        n = ((-1 + u * (1 - (mpz(1) << l0))) % mod) % (mpz(1) << N)
    r = runs2(n)
    return r[0] + r[2], int(n).bit_length() <= N and n > 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'brute':
        def brute(N):
            return max(runs2(n)[0] + runs2(n)[2] for n in range(1, 1 << N, 2))
        for N in range(4, int(a[1]) + 1):
            b = brute(N)
            res = []
            for V in (b - 1, b, b + 1):
                if V - N < 1:
                    continue
                best, hits, st = check(N, V, 2, KSmax=int(a[2]) if len(a) > 2 else 30, verbose=False)
                res.append((V, best))
            ok = all((best == b) if V <= b else best is None for V, best in res)
            print(N, b, res, 'OK' if ok else 'MISMATCH', flush=True)
    else:
        nth = int(a[0])
        outf = a[1]
        pts = json.loads(a[2])        # list of [N, claimed]
        for N, B in pts:
            best, hits, st = check(N, B, nth)
            w = None
            if hits:
                h = max(hits, key=lambda h: h[1])
                w = witness(N, *h[0])
            rec = dict(N=N, claimed=B, mine=best, ok=best == B, above=[h for h in hits if h[1] > B],
                       nhits=len(hits), witness=w, **{k: x for k, x in st.items() if k not in ("N", "V")})
            print(json.dumps(rec), flush=True)
            with open(outf, 'a') as f:
                f.write(json.dumps(rec) + '\n')
