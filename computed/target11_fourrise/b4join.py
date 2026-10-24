"""Exact four-rise bound B4(N) = max over odd n < 2^N of k0 + k1 + k2 + k3  (target 10).

r-rise Theorem (WRITEUP.md section 2; r = 4 case): with u_k = (2/3)^k in Z_2, K1 = k0 + k1,
K2 = K1 + k2, lam = l0 + l1 + l2,
  nu(sigma) = -1 + u_k0 (1 - 2^l0) + 2^l0 u_K1 (1 - 2^l1) + 2^(l0+l1) u_K2 (1 - 2^l2)
has parity vector 1^k0 0^l0 1^k1 0^l1 1^k2 0^l2 1^inf, and an odd n has runs sigma and k3 >= j iff
n == nu (mod 2^(P3 + j)), P3 = K2 + lam.  Hence an odd n < 2^N with value k0+..+k3 >= N + t satisfies
n == nu(sigma(n)) mod 2^(N + t + lam), i.e. bits [N, N + t + lam) of nu(sigma(n)) are 0, and
n = nu(sigma(n)) mod 2^N.

Search (a superset filter; every hit is then checked by literally simulating n = nu mod 2^N):
  bits [N+l0, N+l0+R) of nu, R = min(64, t + l1 + l2), are the low R bits of  P + Q + e  where
    P(k0, l0)          = ALL + W(u_k0, N+l0) - W(u_k0, N)                         (the -1 and X0 terms)
    Q(K1, l1, K2, l2)  = W(u_K1, N) - W(u_K1, N-l1) + W(u_K2, N-l1) - W(u_K2, N-l1-l2)
  (W(x, q) = bits [q, q+64) of x, bits below 0 are 0) and e in [-3, 3] collects the floors of the
  seven fractional parts (4 positive, 3 negative; the -1 term's is ~1).  So it is a JOIN of the
  P list (~N^2/2, hashed on its low s bits) against the Q items, which are enumerated over the
  4-simplex  K1 < K2,  l1 <= N+63-K1,  K2 <= N+63-l1,  l2 <= N+63-l1-K2  (~(N+64)^4/24 items) plus
  GROUP items where the remaining terms have valuation >= N+64 relative to the window and vanish
  mod 2^(N+l0+64), so Q no longer depends on the remaining parameters:
    G1(K1):        l1 >= N+64-K1          Q = W(u_K1, N)
    G2(K1,l1):     K2 >= N+64-l1          Q = W(u_K1, N) - W(u_K1, N-l1)
    G3(K1,l1,K2):  l2 >= N+64-l1-K2       Q = ... + W(u_K2, N-l1)
  (For a group, R uses the least l of the group, which only weakens the filter.)
  Ranges: k0 + l0 <= N - 1 for the P list; k0 + l0 >= N ("region C") forces n = (-1 + u_k0) mod 2^N
  and those N integers are simulated directly.  K1 <= k0 + k1 < N + (delta-1) N + 1 (k0 <= N and
  n1 + 1 <= 3^k0 2^(N-k0)), so K1 <= KMAX1 = ceil(2.585 N) + 2 covers every odd n < 2^N.
  Hits pass a second necessary filter in numba (bits [N, N + min(64, t+lam)) of nu, using l0),
  then the candidate n = nu mod 2^N is simulated with Python ints.
Result: every odd n < 2^N with value >= N + t is found, so B4(N) = best found whenever
best >= N + t - 1 (else rerun with smaller t).
"""
import sys, os, time, math
import numpy as np
import numba as nb
from numba import njit, prange

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)
EOFF = np.array([(e % 2 ** 64) for e in range(-3, 4)], dtype=np.uint64)   # e = -3..3 mod 2^64


def utable(Kmax, L):
    """row K = u_K mod 2^L as little-endian uint64 words"""
    W = (L + 63) // 64 + 2
    M = 1 << (64 * (W - 2))
    inv3 = pow(3, -1, M)
    U = np.zeros((Kmax + 1, W), dtype=np.uint64)
    ints = []
    u = 1
    for K in range(Kmax + 1):
        ints.append(u)
        x = u
        for w in range(W - 2):
            U[K, w] = x & 0xFFFFFFFFFFFFFFFF
            x >>= 64
        u = (u * 2 * inv3) % M
    return U, ints


@njit(inline='always')
def ones(n):
    if n >= 64:
        return ALL
    if n <= 0:
        return U64(0)
    return (U64(1) << U64(n)) - U64(1)


@njit(inline='always')
def win(U, k, pos):
    if pos >= 0:
        w = pos >> 6
        s = pos & 63
        lo = U[k, w] >> U64(s)
        if s == 0:
            return lo
        return lo | (U[k, w + 1] << U64(64 - s))
    if pos <= -64:
        return U64(0)
    return U[k, 0] << U64(-pos)


@njit
def build_P(U, N, s):
    n = 0
    for k0 in range(1, N - 1):
        n += N - 1 - k0
    keys = np.empty(n, dtype=np.uint64)
    ids = np.empty(n, dtype=np.int64)
    i = 0
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            keys[i] = ALL + win(U, k0, N + l0) - win(U, k0, N)
            ids[i] = (k0 << 20) | l0
            i += 1
    sm = ones(s)
    b = (keys & sm).astype(np.int64)
    order = np.argsort(b, kind='mergesort')
    keys = keys[order]
    ids = ids[order]
    b = b[order]
    d = np.zeros((1 << s) + 1, dtype=np.int64)
    for j in range(n):
        d[b[j] + 1] += 1
    for j in range(1 << s):
        d[j + 1] += d[j]
    return keys, ids, d


@njit(inline='always')
def nuwin_ok(U, N, k0, l0, K1, l1, K2, l2, kind, R2):
    """some e in [-3,3] makes the low R2 bits of the window of nu at N vanish (kind: 0 explicit,
    1 = G1, 2 = G2, 3 = G3; dropped terms vanish)"""
    w = ALL + win(U, k0, N) - win(U, k0, N - l0) + win(U, K1, N - l0)
    if kind != 1:
        w = w - win(U, K1, N - l0 - l1)
        if kind != 2:
            w = w + win(U, K2, N - l0 - l1)
            if kind != 3:
                w = w - win(U, K2, N - l0 - l1 - l2)
    mk = ones(R2)
    for ei in range(7):
        if ((w + EOFF[ei]) & mk) == U64(0):
            return True
    return False


@njit(inline='always')
def probe(U, N, t, keys, ids, d, s, Q, R, K1, l1, K2, l2, kind, out, cnt, cap, skip):
    # t here is t_eff = max(t, K2(min) + 1 - N): feasibility z_N(nu) > P3 = K2 + lam
    mk = ones(R)
    sm = ones(s)
    for ei in range(7):
        T = U64(0) - (Q + EOFF[ei])
        b = np.int64(T & sm)
        for j in range(d[b], d[b + 1]):
            if ((keys[j] ^ T) & mk) == U64(0):
                k0 = ids[j] >> 20
                l0 = ids[j] & 0xFFFFF
                if k0 >= K1:
                    continue
                lam = l0 + l1 + (l2 if (kind == 0 or kind == 3) else 1)
                R2 = t + lam
                if R2 > 64:
                    R2 = 64
                if not nuwin_ok(U, N, k0, l0, K1, l1, K2, l2, kind, R2):
                    continue
                if cnt >= skip and cnt - skip < cap:
                    j2 = cnt - skip
                    out[j2, 0] = k0
                    out[j2, 1] = l0
                    out[j2, 2] = K1
                    out[j2, 3] = l1
                    out[j2, 4] = K2
                    out[j2, 5] = l2
                    out[j2, 6] = kind
                cnt += 1
    return cnt


@njit(parallel=True)
def join(U, N, t, keys, ids, d, s, K1s, cap, skips):
    nK = len(K1s)
    out = np.zeros((nK, cap, 7), dtype=np.int64)
    cnts = np.zeros(nK, dtype=np.int64)
    work = np.zeros(nK, dtype=np.int64)
    for iK in prange(nK):
        K1 = K1s[iK]
        cnt = 0
        wk = 0
        o = out[iK]
        WK1 = win(U, K1, N)
        # G1
        l1min = N + 64 - K1
        if l1min < 1:
            l1min = 1
        te = max(t, K1 + 2 - N)
        R = te + l1min + 1
        if R > 64:
            R = 64
        cnt = probe(U, N, te, keys, ids, d, s, WK1, R, K1, l1min, 0, 0, 1, o, cnt, cap, skips[iK])
        for l1 in range(1, N + 64 - K1):
            Qa = WK1 - win(U, K1, N - l1)
            # G2
            K2min = N + 64 - l1
            if K2min < K1 + 1:
                K2min = K1 + 1
            te = max(t, K2min + 1 - N)
            R = te + l1 + 1
            if R > 64:
                R = 64
            cnt = probe(U, N, te, keys, ids, d, s, Qa, R, K1, l1, K2min, 0, 2, o, cnt, cap, skips[iK])
            for K2 in range(K1 + 1, N + 64 - l1):
                Qb = Qa + win(U, K2, N - l1)
                l2min = N + 64 - l1 - K2
                if l2min < 1:
                    l2min = 1
                te = max(t, K2 + 1 - N)
                R = te + l1 + l2min
                if R > 64:
                    R = 64
                cnt = probe(U, N, te, keys, ids, d, s, Qb, R, K1, l1, K2, l2min, 3, o, cnt, cap, skips[iK])
                for l2 in range(1, N + 64 - l1 - K2):
                    Q = Qb - win(U, K2, N - l1 - l2)
                    R = te + l1 + l2
                    if R > 64:
                        R = 64
                    cnt = probe(U, N, te, keys, ids, d, s, Q, R, K1, l1, K2, l2, 0, o, cnt, cap, skips[iK])
                    wk += 1
        cnts[iK] = cnt
        work[iK] = wk
    return out, cnts, work


def runs_value(n, r=4):
    """literal: sum of the first r rises of odd n"""
    tot = 0
    for _ in range(r):
        x = n + 1
        k = (x & -x).bit_length() - 1
        tot += k
        y = 3 ** k * (x >> k) - 1
        l = (y & -y).bit_length() - 1
        n = y >> l
    return tot


PAGE = 0      # tests set this small to force paging


def B4(N, t, verbose=False, cap=None, want_set=False):
    t0 = time.time()
    K1max = math.ceil(2.585 * N) + 2
    L = 2 * N + 192
    U, ints = utable(K1max + 70, L)
    MN = (1 << N) - 1
    best, wit = -1, None
    # region C
    for k0 in range(1, N + 1):
        n = (-1 + ints[k0]) & MN
        v = runs_value(n)
        if v > best:
            best, wit = v, n
    if cap is None:
        cap = max(64, int(1.5e6 / (K1max + 1)))
    s = max(0, min(20, t + 2))
    keys, ids, d = build_P(U, N, s)
    t1 = time.time()
    K1s = np.arange(2, K1max + 1, dtype=np.int64)
    zero = np.zeros(len(K1s), dtype=np.int64)
    out, cnts, work = join(U, N, t, keys, ids, d, s, K1s, cap, zero)
    t2 = time.time()
    nh = 0
    found = 0
    fset = set()
    for k0 in range(1, N + 1):
        n = (-1 + ints[k0]) & MN
        if runs_value(n) >= N + t:
            fset.add(n)

    def process(outp, cntp):
        nonlocal nh, found, best, wit
        for iK in range(len(cntp)):
            for i in range(cntp[iK]):
                k0, l0, K1_, l1, K2, l2, kind = (int(x) for x in outp[iK, i])
                nu = -1 + ints[k0] - (ints[k0] << l0) + (ints[K1_] << l0)
                if kind != 1:
                    nu -= ints[K1_] << (l0 + l1)
                    if kind != 2:
                        nu += ints[K2] << (l0 + l1)
                        if kind != 3:
                            nu -= ints[K2] << (l0 + l1 + l2)
                n = nu & MN
                v = runs_value(n)
                nh += 1
                if v >= N + t:
                    found += 1
                    fset.add(n)
                if v > best:
                    best, wit = v, n

    process(out, np.minimum(cnts, cap))
    # K1 whose hit count exceeds the buffer: re-run those K1 alone, page by page (hit number
    # skip .. skip+cap-1 of each K1's deterministic hit sequence), verifying each page literally.
    over = K1s[cnts > cap]
    totals = cnts[cnts > cap]
    npage = 0
    cap2 = PAGE if PAGE else max(2000, int(1e7) // max(1, len(over)))
    skip = np.full(len(over), cap, dtype=np.int64)
    while len(over):
        o2, c2, _ = join(U, N, t, keys, ids, d, s, over, cap2, skip)
        assert (c2 == totals).all()
        process(o2, np.clip(totals - skip, 0, cap2))
        npage += 1
        skip = skip + cap2
        keep = totals > skip
        over, totals, skip = over[keep], totals[keep], skip[keep]
        del o2
    t3 = time.time()
    if verbose:
        print(f"N={N} t={t} |P|={len(keys)} items={int(work.sum())} hits={nh} (value>=N+t: {found}) pages={npage} "
              f"best={best} (N+{best - N})  t_prep={t1 - t0:.1f}s t_join={t2 - t1:.1f}s t_check={t3 - t2:.1f}s",
              flush=True)
    if want_set:
        return best, wit, best >= N + t - 1, fset
    return best, wit, best >= N + t - 1


def exact(N, t=None, verbose=True):
    if t is None:
        t = max(-8, math.floor(3 * math.log2(N) - math.log2(6) - 6)) if N > 8 else -8
    while True:
        try:
            best, wit, ok = B4(N, t, verbose)
        except RuntimeError as ex:
            if verbose:
                print(f"  t={t}: {ex}; retry with t+3", flush=True)
            t += 3
            continue
        if ok:
            assert runs_value(wit) == best and 0 < wit < (1 << N) and wit % 2 == 1
            return best, wit, t
        t = best - N + 1 if best - N + 1 < t else t - 4


if __name__ == "__main__":
    for N in map(int, sys.argv[1:]):
        b, w, t = exact(N)
        print(f"B4({N}) = {b}  (N+{b - N})  witness n={w}", flush=True)
