"""Referee (target 11): independent search for odd n < 2^N whose first four rises total >= V.

Written from Theorem R (r = 4) and Fact P only; not derived from b4join.py.  Different decomposition:
the join is split after the SECOND block (first half = blocks 0,1 = (k0,l0,K1,l1); second half = block 2
= (K2,l2), at shift h = l0 + l1), hashing the second half per h; b4join splits after the first block.

Math.  sigma = (k0,l0,k1,l1,k2,l2), K1 = k0+k1, K2 = K1+k2, h = l0+l1, lam = h+l2, u_b = (2/3)^b in Z_2,
  nu = -1 + u_k0 - 2^l0 u_k0 + 2^l0 u_K1 - 2^h u_K1 + 2^h u_K2 - 2^lam u_K2.
If odd n < 2^N has runs sigma and k3, value v = K2 + k3 >= V, then (Fact P + parity vector of nu)
n == nu mod 2^(v+lam) and v + lam >= V + 3, so with R := V - N + 3 (if R >= 1):
  (a) n = nu mod 2^N,   (b) bits [N, N+R) of nu are 0.
Window arithmetic: put M = N + R.  Each of the 7 terms T_j = +-2^a u_b has (T_j mod 2^M) = 2^N w_j + r_j,
0 <= r_j < 2^N; so bits [N, N+R) of nu = (sum +-w_j + e) mod 2^R with e = floor(sum +-r_j / 2^N) in [-3, 3]
(4 terms with +, 3 with -; the -1 term is +(2^M - 1)).  A term with a + b >= M is 0 mod 2^M: dropped
(and then it is also 0 mod 2^N, so (a) is computed without it).  Classes of sigma (a partition):
  k0 >= M            -> nu == -1 mod 2^M: candidate n = 2^N - 1
  l0 >= M - k0       -> G1(k0)            candidate from -1 + u_k0
  K1 >= M - l0       -> G2(k0,l0)         from -1 + u_k0 - 2^l0 u_k0
  h  >= M - K1       -> G3(k0,l0,K1)      ... + 2^l0 u_K1
  else first half explicit (k0 < K1, l0 + K1 < M, h + K1 < M), joined against, for this h:
  K2 >= M - h        -> D = 0             (one table entry, 'kind 2')
  l2 >= M - h - K2   -> D = 2^h u_K2      (entry (K2, kind 1))
  else               -> D = 2^h u_K2 - 2^lam u_K2  (entry (K2, l2, kind 0))
Every passing item is turned into its candidate n = nu mod 2^N (big ints) and SIMULATED literally.
So the returned set contains every odd n < 2^N with value >= V; the reported values are literal.
usage: python refb4.py N V      (prints all n found with value >= V, and the max)
"""
import sys, time, math
import numpy as np
import numba as nb
from numba import njit, prange

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)
EO = np.array([e % 2 ** 64 for e in range(-3, 4)], dtype=np.uint64)   # e = -3..3 mod 2^64


def utab(bmax, nbits):
    W = nbits // 64 + 3
    mod = 1 << (64 * W)
    i3 = pow(3, -1, mod)
    T = np.zeros((bmax + 1, W), dtype=np.uint64)
    big = []
    u = 1
    for b in range(bmax + 1):
        big.append(u)
        x = u
        for w in range(W):
            T[b, w] = x & 0xFFFFFFFFFFFFFFFF
            x >>= 64
        u = (2 * u * i3) % mod
    return T, big


@njit(inline='always')
def wnd(T, b, pos):
    """bits [pos, pos+64) of u_b (bits at negative positions are 0)"""
    if pos >= 0:
        q = pos >> 6
        s = pos & 63
        if s == 0:
            return T[b, q]
        return (T[b, q] >> U64(s)) | (T[b, q + 1] << U64(64 - s))
    if pos <= -64:
        return U64(0)
    return T[b, 0] << U64(-pos)


@njit(inline='always')
def zmask(R):
    if R >= 64:
        return ALL
    return (U64(1) << U64(R)) - U64(1)


@njit
def selfgroups(T, N, M, R, out, cap):
    """G2(k0,l0) and G3(k0,l0,K1): no join.  out rows (k0,l0,K1,kind)"""
    mk = zmask(R)
    c = 0
    for k0 in range(1, M):
        base = ALL + wnd(T, k0, N)
        for l0 in range(1, M - k0):
            a = base - wnd(T, k0, N - l0)
            # G2: K1 >= M - l0 (any K1 > k0)
            hit = False
            for e in range(7):
                if ((a + EO[e]) & mk) == U64(0):
                    hit = True
            if hit:
                if c < cap:
                    out[c, 0] = k0; out[c, 1] = l0; out[c, 2] = -1; out[c, 3] = 2
                c += 1
            for K1 in range(k0 + 1, M - l0):
                b = a + wnd(T, K1, N - l0)
                # G3: h >= M - K1, h = l0 + l1 > l0
                hit = False
                for e in range(7):
                    if ((b + EO[e]) & mk) == U64(0):
                        hit = True
                if hit:
                    if c < cap:
                        out[c, 0] = k0; out[c, 1] = l0; out[c, 2] = K1; out[c, 3] = 3
                    c += 1
    return c


@njit
def dtable(T, N, M, h, s):
    """second-half entries for shift h, bucketed on the low s bits"""
    n = 1
    for K2 in range(3, M - h):
        n += 1 + max(0, M - h - K2 - 1)
    keys = np.empty(n, dtype=np.uint64)
    meta = np.empty((n, 3), dtype=np.int64)     # K2, l2, kind
    i = 0
    keys[i] = U64(0); meta[i, 0] = -1; meta[i, 1] = -1; meta[i, 2] = 2; i += 1
    for K2 in range(3, M - h):
        wa = wnd(T, K2, N - h)
        keys[i] = wa; meta[i, 0] = K2; meta[i, 1] = -1; meta[i, 2] = 1; i += 1
        for l2 in range(1, M - h - K2):
            keys[i] = wa - wnd(T, K2, N - h - l2)
            meta[i, 0] = K2; meta[i, 1] = l2; meta[i, 2] = 0; i += 1
    sm = zmask(s)
    bk = (keys & sm).astype(np.int64)
    order = np.argsort(bk, kind='mergesort')
    keys = keys[order]; meta = meta[order]; bk = bk[order]
    start = np.zeros((1 << s) + 1, dtype=np.int64)
    for j in range(n):
        start[bk[j] + 1] += 1
    for j in range(1 << s):
        start[j + 1] += start[j]
    return keys, meta, start


@njit(parallel=True)
def probe_h(T, N, M, R, h, keys, meta, start, s, K1list, out, cap):
    """explicit first-half items with l0 + l1 = h, K1 in K1list (prange).  out[iK, c] = (k0, l0, K1, K2, l2, kind)"""
    mk = zmask(R)
    sm = zmask(s)
    nK = len(K1list)
    cnt = np.zeros(nK, dtype=np.int64)
    work = np.zeros(nK, dtype=np.int64)
    for iK in prange(nK):
        K1 = K1list[iK]
        c = 0
        wk = 0
        wKh = wnd(T, K1, N - h)
        for k0 in range(1, K1):
            base = ALL + wnd(T, k0, N) - wKh
            for l0 in range(1, h):
                if l0 + K1 >= M:
                    break
                A = base - wnd(T, k0, N - l0) + wnd(T, K1, N - l0)
                wk += 1
                for e in range(7):
                    tgt = (U64(0) - A - EO[e]) & mk
                    b = np.int64(tgt & sm)
                    for j in range(start[b], start[b + 1]):
                        if (keys[j] & mk) == tgt:
                            kind = meta[j, 2]
                            if kind != 2 and meta[j, 0] <= K1:
                                continue
                            if c < cap:
                                out[iK, c, 0] = k0; out[iK, c, 1] = l0; out[iK, c, 2] = K1
                                out[iK, c, 3] = meta[j, 0]; out[iK, c, 4] = meta[j, 1]; out[iK, c, 5] = kind
                            c += 1
        cnt[iK] = c
        work[iK] = wk
    return cnt, work


def value4(n):
    """literal: k0+k1+k2+k3 of odd n via n+1 = 2^k a, next min = (3^k a - 1)/2^l"""
    v = 0
    for i in range(4):
        x = n + 1
        k = (x & -x).bit_length() - 1
        v += k
        if i == 3:
            break
        y = 3 ** k * (x >> k) - 1
        n = y >> ((y & -y).bit_length() - 1)
    return v


def search(N, V, threads=None, verbose=True, cap=256):
    """all odd n < 2^N with value4(n) >= V (complete), as dict n -> value; plus stats"""
    if threads:
        nb.set_num_threads(threads)
    R = V - N + 3
    t0 = time.time()
    found = {}
    stats = dict(cand=0)
    MN = (1 << N) - 1

    def test(n):
        stats['cand'] += 1
        assert n & 1 and 0 < n < (1 << N)
        v = value4(n)
        if v >= V:
            found[n] = v
    if R < 1:
        for n in range(1, 1 << N, 2):     # no filter possible: brute force (only for tiny N)
            test(n)
        return found, stats
    M = N + R
    T, big = utab(M + 2, N + 192)
    test(MN)                               # k0 >= M  (and k0 >= N in general)
    for k0 in range(1, M):                 # G1(k0)
        test((-1 + big[k0]) & MN)
    cap1 = 1 << 20
    out = np.zeros((cap1, 4), dtype=np.int64)
    c = selfgroups(T, N, M, R, out, cap1)
    assert c <= cap1, c
    for k0, l0, K1, kind in out[:c]:
        k0, l0, K1 = int(k0), int(l0), int(K1)
        x = -1 + big[k0] - (big[k0] << l0)
        if kind == 3:
            x += big[K1] << l0
        test(x & MN)
    stats['self'] = int(c)
    s = max(0, min(18, R))
    nh = 0
    work = 0
    for h in range(2, M - 2):
        K1s = np.arange(2, M - h, dtype=np.int64)
        if len(K1s) == 0:
            continue
        keys, meta, start = dtable(T, N, M, h, s)
        K1s = K1s[np.random.RandomState(h).permutation(len(K1s))]
        o = np.zeros((len(K1s), cap, 6), dtype=np.int64)
        cnt, wk = probe_h(T, N, M, R, h, keys, meta, start, s, K1s, o, cap)
        work += int(wk.sum())
        rows = [o[iK, :cnt[iK]] for iK in range(len(K1s)) if cnt[iK] <= cap]
        over = K1s[cnt > cap]
        for K1 in over:             # re-run an overflowing K1 alone with a buffer of its exact size
            c1 = int(cnt[K1s == K1][0])
            o1 = np.zeros((1, c1, 6), dtype=np.int64)
            cc, _ = probe_h(T, N, M, R, h, keys, meta, start, s, np.array([K1], dtype=np.int64), o1, c1)
            assert cc[0] == c1
            rows.append(o1[0])
            stats['overflowK1'] = stats.get('overflowK1', 0) + 1
        for blk in rows:
            for row in blk:
                k0, l0, K1, K2, l2, kind = (int(x) for x in row)
                x = -1 + big[k0] - (big[k0] << l0) + (big[K1] << l0) - (big[K1] << h)
                if kind != 2:
                    x += big[K2] << h
                    if kind == 0:
                        x -= big[K2] << (h + l2)
                test(x & MN)
                nh += 1
    stats.update(joinhits=nh, items=work, secs=round(time.time() - t0, 1), R=R, M=M)
    if verbose:
        print(f"N={N} V={V} R={R} items={work:.3e} joinhits={nh} self={stats['self']} cand={stats['cand']} "
              f"found={len(found)} max={max(found.values()) if found else None} {time.time() - t0:.1f}s", flush=True)
    return found, stats


def exact(N, start_V, threads=None):
    """B4(N): search at V = start_V, V-1, ... until something is found; the max found is B4."""
    V = start_V
    while True:
        f, _ = search(N, V, threads)
        if f:
            return max(f.values()), f
        V -= 1


if __name__ == "__main__":
    N, V = int(sys.argv[1]), int(sys.argv[2])
    th = int(sys.argv[3]) if len(sys.argv) > 3 else None
    f, st = search(N, V, th)
    best = max(f.values()) if f else None
    print(f"RESULT N={N} V={V}: {len(f)} odd n < 2^N with value >= V; max value {best}; "
          f"witnesses {sorted(f.items(), key=lambda x: -x[1])[:3]}", flush=True)
