"""Referee (target 7b): own exact search for three-rise values  B3(N) >= V ?

Theorem 1 (target7_threerise, refereed):  nu(s) = -1 + u_k0 (1 - 2^l0) + 2^l0 u_K (1 - 2^l1),
u_k = (2/3)^k in Z_2, K = k0+k1, lam = l0+l1, P2 = K+lam;  B3(N) = max{ z_N(nu) - lam : z_N(nu) > P2 }.

find(N, V, KQ) returns every VALID sigma with value >= V (exact), where KQ >= B2(N) bounds K = k0+k1.
Decomposition (own):
 * region C (k0 + l0 >= N):  the n < 2^N is nu mod 2^N = (u_k0 - 1) mod 2^N (2^l0 * anything = 0
   mod 2^N), one n per k0 in 1..N; each is SIMULATED LITERALLY (three runs).  This covers every valid
   sigma with k0 + l0 >= N.
 * k0 + l0 < N:  value >= V  =>  bits [N+l0, N+l0+t+l1) of nu are 0  (t = V - N >= 1).
   nu >> (N+l0) = (X >> (N+l0)) + (W >> N) + c,  X = (u_k0 - 1) - 2^l0 u_k0,  W = u_K - 2^l1 u_K,
   X >> (N+l0) = (u_k0 >> (N+l0)) - (u_k0 >> N) - bX,   W >> N = (u_K >> N) - (u_K >> (N-l1)) - bW
   (2-adic floor shifts; bX, bW in {0,1} borrows, c in {0,1} carry: NOT computed, all 4 offsets
   o = c - bX - bW in {-2,-1,0,1} are tried).  With P = win(u_k0, N+l0) - win(u_k0, N) and
   Q = win(u_K, N) - win(u_K, N-l1) (mod 2^64): need P + Q + o = 0 mod 2^w, w = min(64, t + l1).
   Explicit l1 = 1 .. N+63-K;  for l1 >= N+64-K, win(u_K, N-l1) = 0 (one 'group' item per K, w=64),
   and validity forces l1 = z_N(nu') - K - l0 with nu' = -1 + u_k0(1-2^l0) + 2^l0 u_K (K < V assumed).
   Join: P list partitioned by its low s bits, then bucketed (counting sort) by the next r0 bits of
   the bit-reversed key; each Q item probes the buckets of its 4 targets.  Matches pass a second
   necessary filter (bits [N, N+min(64,t+lam)) of nu zero, 4 offsets) and are evaluated EXACTLY.
"""
import sys, os, time, math, json
import numpy as np
import numba as nb
from numba import njit, prange
import gmpy2
from fractions import Fraction as F
from gmpy2 import mpz

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)


def build_U(KM, M):
    """rows k = 0..KM: u_k = 2^k 3^-k mod 2^M as little-endian uint64 limbs (M multiple of 64)"""
    mod = mpz(1) << M
    w2 = (2 * gmpy2.invert(mpz(3), mod)) % mod
    nl = M // 64
    U = np.zeros((KM + 1, nl), dtype=np.uint64)
    u = mpz(1)
    for k in range(KM + 1):
        U[k, :] = np.frombuffer(int(u).to_bytes(nl * 8, 'little'), dtype=np.uint64)
        u = (u * w2) % mod
    return U


@njit(inline='always')
def win(U, k, pos):
    if pos >= 0:
        w = pos >> 6
        s = pos & 63
        lo = U[k, w] >> U64(s)
        if s != 0:
            lo |= U[k, w + 1] << U64(64 - s)
        return lo
    if pos <= -64:
        return U64(0)
    return U[k, 0] << U64(-pos)


@njit(inline='always')
def lowmask(w):
    if w >= 64:
        return ALL
    return (U64(1) << U64(w)) - U64(1)


@njit(inline='always')
def brev(x):
    m1 = U64(0x5555555555555555); m2 = U64(0x3333333333333333); m4 = U64(0x0F0F0F0F0F0F0F0F)
    m8 = U64(0x00FF00FF00FF00FF); m16 = U64(0x0000FFFF0000FFFF)
    x = ((x & m1) << U64(1)) | ((x >> U64(1)) & m1)
    x = ((x & m2) << U64(2)) | ((x >> U64(2)) & m2)
    x = ((x & m4) << U64(4)) | ((x >> U64(4)) & m4)
    x = ((x & m8) << U64(8)) | ((x >> U64(8)) & m8)
    x = ((x & m16) << U64(16)) | ((x >> U64(16)) & m16)
    return (x << U64(32)) | (x >> U64(32))


@njit
def fill_part(U, N, s, j, r0, count_only, rev, ids, d):
    """P items with low s bits == j; counting-sort by bucket (next r0 bits of bit-reversed key)"""
    sm = lowmask(s)
    n = 0
    if count_only:
        for k0 in range(1, N - 1):
            for l0 in range(1, N - k0):
                P = win(U, k0, N + l0) - win(U, k0, N)
                if (P & sm) == U64(j):
                    n += 1
        return n
    # bucket counts
    for b in range(d.shape[0]):
        d[b] = 0
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            P = win(U, k0, N + l0) - win(U, k0, N)
            if (P & sm) == U64(j):
                rv = brev(P)
                b = (rv << U64(s)) >> U64(64 - r0) if s > 0 else rv >> U64(64 - r0)
                d[b + 1] += 1
    for b in range(d.shape[0] - 1):
        d[b + 1] += d[b]
    pos = d.copy()
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            P = win(U, k0, N + l0) - win(U, k0, N)
            if (P & sm) == U64(j):
                rv = brev(P)
                b = (rv << U64(s)) >> U64(64 - r0) if s > 0 else rv >> U64(64 - r0)
                i = pos[b]
                rev[i] = rv
                ids[i] = (k0 << 16) | l0
                pos[b] += 1
    return d[d.shape[0] - 1]


@njit
def second_ok(U, N, t, k0, l0, K, l1):
    """bits [N, N + min(64, t+lam)) of nu are zero for some offset in {-2..1}"""
    S = win(U, k0, N) - win(U, k0, N - l0) + win(U, K, N - l0) - win(U, K, N - l0 - l1)
    m = lowmask(t + l0 + l1)
    for oo in range(4):
        if (((S + U64(oo)) - U64(2)) & m) == U64(0):
            return True
    return False


@njit(parallel=True)
def probe(U, N, t, KQ, s, j, r0, rev, ids, d, out, cnt, nthreads, Kstart):
    """for every Q item (K, l1) [and group item, l1 = -1], probe the 4 targets in partition j.
    out[th, i] = (k0, l0, K, l1) for matches passing the second filter; cnt[th, 0] = #stored,
    cnt[th, 1] = #first-stage matches"""
    sm = lowmask(s)
    cap = out.shape[1]
    nK = KQ - Kstart + 1
    for ii in prange(nK):
        K = Kstart + ii
        th = nb.get_thread_id()
        lmax = N + 63 - K
        for l1 in range(1, lmax + 2):
            group = l1 == lmax + 1
            if group:
                Q = win(U, K, N)
                w = 64
            else:
                Q = win(U, K, N) - win(U, K, N - l1)
                w = t + l1
                if w > 64:
                    w = 64
            for oo in range(4):
                T = ((U64(0) - Q) - U64(oo)) + U64(2)
                if (T & sm) != U64(j):
                    continue
                rt = brev(T)
                if w >= s + r0:
                    b = (rt << U64(s)) >> U64(64 - r0) if s > 0 else rt >> U64(64 - r0)
                    lo, hi = d[b], d[b + 1]
                    full = False
                else:
                    sh = s + r0 - w
                    b = (rt << U64(s)) >> U64(64 - r0) if s > 0 else rt >> U64(64 - r0)
                    b0 = (b >> U64(sh)) << U64(sh)
                    lo, hi = d[b0], d[b0 + (1 << sh)]
                    full = True
                for i in range(lo, hi):
                    if not full:
                        if w == 64:
                            if rev[i] != rt:
                                continue
                        elif ((rev[i] ^ rt) >> U64(64 - w)) != U64(0):
                            continue
                    k0 = ids[i] >> 16
                    l0 = ids[i] & 0xFFFF
                    if k0 >= K:
                        continue
                    cnt[th, 1] += 1
                    if not group:
                        if not second_ok(U, N, t, k0, l0, K, l1):
                            continue
                    c = cnt[th, 0]
                    if c < cap:
                        out[th, c, 0] = k0
                        out[th, c, 1] = l0
                        out[th, c, 2] = K
                        out[th, c, 3] = l1 if not group else -1
                    cnt[th, 0] = c + 1


# ---------------- exact evaluation ----------------
_U = {}


def u_exact(k, R):
    """(2/3)^k mod 2^R"""
    return (pow(mpz(3), -k, mpz(1) << R) << k) % (mpz(1) << R)


def zN(x, N, R):
    """least i >= N with bit i of x set (x known mod 2^R); None if bits [N, R) all zero"""
    y = x >> N
    if y == 0:
        return None
    return N + gmpy2.bit_scan1(y)


def nu_exact(k0, l0, K, l1, R):
    mod = mpz(1) << R
    a = u_exact(k0, R)
    b = u_exact(K, R)
    if l1 is None:
        return (-1 + a * (1 - (mpz(1) << l0)) + (b << l0)) % mod
    return (-1 + a * (1 - (mpz(1) << l0)) + ((b * (1 - (mpz(1) << l1))) << l0)) % mod


def value_exact(N, k0, l0, K, l1):
    """(z_N(nu), value, valid) exactly"""
    lam = l0 + l1
    R = N + lam + K + 256
    while True:
        nu = nu_exact(k0, l0, K, l1, R)
        z = zN(nu, N, R)
        if z is not None:
            break
        R *= 2
    return z, z - lam, z > K + lam


def runs3(n):
    """literal simulation of T(n) = (3n+1)/2 | n/2 on odd n: (k0,l0,k1,l1,k2)"""
    n = mpz(n)
    out = []
    for r in range(5):
        if r % 2 == 0:
            k = gmpy2.bit_scan0(n)      # n + 1 = 2^k a
            a = (n + 1) >> k
            n = a * mpz(3) ** k - 1
            out.append(k)
        else:
            l = gmpy2.bit_scan1(n)
            n >>= l
            out.append(l)
    return tuple(out)


def regionC(N, V):
    """simulate n = (u_k0 - 1) mod 2^N, k0 = 1..N; returns (best value, list of (sigma, value) >= V)"""
    mod = mpz(1) << N
    w2 = (2 * gmpy2.invert(mpz(3), mod)) % mod
    u = mpz(1)
    best, hits = -1, []
    for k0 in range(1, N + 1):
        u = (u * w2) % mod
        n = (u - 1) % mod
        if n == 0:
            continue
        assert n & 1
        r = runs3(n)
        assert r[0] == k0 or k0 == N, (k0, r)
        v = r[0] + r[2] + r[4]
        if v > best:
            best = v
        if v >= V:
            hits.append(((r[0], r[1], r[2], r[3]), v, int(n)))
    return best, hits


def find(N, V, KQ, nthreads=4, verbose=True, cap=1 << 19, force=None, Ksmall=24):
    t = V - N
    assert t >= 1
    assert KQ < V, "validity shortcut for group items needs K < V"
    T0 = time.time()
    KM = max(N, KQ) + 1
    M = ((2 * N + 64 + 128) // 64 + 1) * 64
    U = build_U(KM, M)
    nP = (N - 2) * (N - 1) // 2
    s = 0
    while (nP >> s) > 40_000_000 and s < t:
        s += 1
    s = min(s, t)
    per = max(1, nP >> s)
    r0 = max(4, min(24, int(math.log2(per)) - 1))
    if force:
        s, r0 = force
    d = np.zeros((1 << r0) + 1, dtype=np.int64)
    nb.set_num_threads(nthreads)
    out = np.zeros((nb.config.NUMBA_NUM_THREADS, cap, 4), dtype=np.int32)
    cnt = np.zeros((nb.config.NUMBA_NUM_THREADS, 2), dtype=np.int64)
    found = []
    first = 0
    # small K (periodic windows -> structured false matches): exhaustive with a rigorous lam bound.
    # n2 + 1 < 3^K (n+1) 2^-P2 + 3^k1 2^-(k1+l1) + 1 <= 3^K 2^(N-K-lam) + 1.5^K + 1, and
    # n2 + 1 >= 2^k2 >= 2^(V-K): so 2^(V-K) - 1.5^K - 1 < 3^K 2^(N-K-lam)  bounds lam.
    Ks = 1
    small = []
    for K in range(2, min(Ksmall, KQ) + 1):
        lhs = F(2) ** (V - K) - F(3, 2) ** K - 1
        if lhs <= 0:
            break
        lam = 0
        while F(3) ** K * F(2) ** (N - K - (lam + 1)) > lhs:
            lam += 1
        # every valid sigma with this K and value >= V has l0 + l1 <= lam
        for k0 in range(1, K):
            for l0 in range(1, lam):
                for l1 in range(1, lam - l0 + 1):
                    small.append((k0, l0, K, l1))
        Ks = K
    for j in range(1 << s):
        n = fill_part(U, N, s, j, r0, True, np.zeros(1, U64), np.zeros(1, np.uint32), d)
        rev = np.zeros(n, dtype=np.uint64)
        ids = np.zeros(n, dtype=np.uint32)
        n2 = fill_part(U, N, s, j, r0, False, rev, ids, d)
        assert n2 == n
        cnt[:] = 0
        probe(U, N, t, KQ, s, j, r0, rev, ids, d, out, cnt, nthreads, Ks + 1)
        assert (cnt[:, 0] <= cap).all(), "output overflow"
        first += int(cnt[:, 1].sum())
        for th in range(cnt.shape[0]):
            for i in range(cnt[th, 0]):
                found.append(tuple(int(x) for x in out[th, i]))
        del rev, ids
        if verbose:
            print(f"   N={N} part {j}/{1 << s} size {n} matches {first} second {len(found)} "
                  f"{time.time() - T0:.0f}s", flush=True)
    # exact evaluation
    hits = []
    ngroup = 0
    for (k0, l0, K, l1) in small + found:
        if l1 == -1:
            ngroup += 1
            R = 4 * N + 512
            nup = nu_exact(k0, l0, K, None, R)
            z = zN(nup, N, R)
            assert z is not None
            l1f = z - K - l0
            if l1f < N + 64 - K:
                continue
            l1 = l1f
        z, v, valid = value_exact(N, k0, l0, K, l1)
        if valid and v >= V:
            hits.append(((k0, l0, K - k0, l1), v))
    cbest, chits = regionC(N, V)
    allhits = hits + [(s_, v) for (s_, v, _) in chits]
    best = max([v for _, v in allhits], default=None)
    stats = dict(N=N, V=V, KQ=KQ, s=s, r0=r0, Ks=Ks, nsmall=len(small), first=first, second=len(found), group=ngroup,
                 nhits=len(allhits), regionC_best=cbest, secs=round(time.time() - T0, 1))
    return best, allhits, stats


def witness_check(N, sigma):
    """rebuild n from sigma via Theorem 1 and simulate literally; returns (n < 2^N, runs)"""
    k0, l0, k1, l1 = sigma
    R = N + 8
    nu = nu_exact(k0, l0, k0 + k1, l1, R + l0 + l1 + k0 + k1 + 64)
    n = nu % (mpz(1) << N)
    return runs3(n), int(n).bit_length() <= N


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'one':
        N, V, KQ = int(a[1]), int(a[2]), int(a[3])
        best, hits, st = find(N, V, KQ, nthreads=int(a[4]) if len(a) > 4 else 4)
        print(best, st)
        for h in sorted(hits, key=lambda h: -h[1])[:10]:
            print("  ", h)
