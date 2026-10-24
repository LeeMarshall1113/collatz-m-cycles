"""Independent referee: B(N) = max over odd n < 2^N of k0 + k1 (see WRITEUP.md).

Usage: python tworise.py brute NMAX        exhaustive check N=2..NMAX vs fast + slow
       python tworise.py fast N [N ...]    exact B(N) via numpy filter + exact verification
       python tworise.py slow N            exact B(N) via pure-bigint per (k,l) (O(N^2) bigint ops)
"""
import sys, time
import numpy as np


def v2(x):
    return (x & -x).bit_length() - 1


def k0k1_direct(n):
    """Literal simulation of T on odd n: returns (k0, l, k1)."""
    assert n & 1
    k0 = 0
    while n & 1:
        n = (3 * n + 1) // 2
        k0 += 1
    l = 0
    while not n & 1:
        n //= 2
        l += 1
    k1 = 0
    while n & 1:
        n = (3 * n + 1) // 2
        k1 += 1
    return k0, l, k1


def brute(N):
    best = 0
    for n in range(1, 1 << N, 2):
        k0, l, k1 = k0k1_direct(n)
        if k0 + k1 > best:
            best = k0 + k1
    return best


def exact_from_a(k, a):
    """k0=k, a odd: return (l, k1) exactly, by integer arithmetic on 3^k a."""
    x = pow(3, k) * a
    l = v2(x - 1)
    k1 = v2(x - 1 + (1 << l)) - l
    return l, k1


def inv3_powers(N, M):
    """yield (k, u_k) with u_k = 3^{-k} mod 2^M, k = 1..N."""
    mask = (1 << M) - 1
    inv3 = (2 * (1 << M) + 1) // 3 if M % 2 == 0 else ((1 << M) + 1) // 3
    assert (3 * inv3) & mask == 1
    u = 1
    for k in range(1, N + 1):
        u = (u * inv3) & mask
        yield k, u


def slow(N):
    """Exact B(N): for each k<N, l in [1, D-1] take candidate p-l; plus l>=D collapse; plus k=N."""
    M = N + 256
    mask = (1 << M) - 1
    best, arg = -1, None
    for k, u in inv3_powers(N, M):
        D = N - k
        if k == N:
            l, k1 = exact_from_a(N, 1)
            cand = [(k + k1, (k, 1, l))]
        else:
            cand = []
            for l in range(1, D):
                r = (u - (u << l)) & mask
                h = r >> D
                assert h != 0
                g = v2(h)
                assert D + g < M
                cand.append((N + g - l, (k, l)))
            a0 = u & ((1 << D) - 1)
            l, k1 = exact_from_a(k, a0)
            assert l >= D
            cand.append((k + k1, (k, a0, l)))
        for c in cand:
            if c[0] > best:
                best, arg = c
    return best, arg


def fast(N, t0=3, verbose=True):
    """Exact B(N).  Pairs (k,l) with excess g-l < t0 are discarded by a provable 64-bit filter;
    the rest are evaluated exactly.  Returns (B, witness, stats)."""
    M = N + 192
    mask = (1 << M) - 1
    nbytes = ((M + 63) // 64 + 2) * 8
    LMAX = N + 1
    lv = np.arange(LMAX, dtype=np.int64)
    tt = lv + t0
    masks = np.where(tt >= 64, np.uint64(0xFFFFFFFFFFFFFFFF),
                     (np.uint64(1) << np.minimum(tt, 63).astype(np.uint64)) - np.uint64(1))
    best, arg = -1, None
    ncand = 0
    excess_hist = {}
    collapse_best = -1
    t_start = time.time()
    for k, u in inv3_powers(N, M):
        D = N - k
        if k == N:
            l, k1 = exact_from_a(N, 1)
            val = k + k1
            collapse_best = max(collapse_best, val)
            if val > best:
                best, arg = val, ("k=N", k, 1, l, k1)
            continue
        # collapse case l >= D: unique a0
        a0 = u & ((1 << D) - 1)
        l, k1 = exact_from_a(k, a0)
        assert l >= D
        val = k + k1
        collapse_best = max(collapse_best, val)
        if val > best:
            best, arg = val, ("collapse", k, a0.bit_length(), l, k1)
        if D < 2:
            continue
        w = np.frombuffer(u.to_bytes(nbytes, "little"), dtype=np.uint64)
        x = int(w[D >> 6] >> np.uint64(D & 63))
        if D & 63:
            x |= (int(w[(D >> 6) + 1]) << (64 - (D & 63))) & 0xFFFFFFFFFFFFFFFF
        x = np.uint64(x)
        ls = np.arange(1, D, dtype=np.int64)          # l = 1..D-1
        s = D - ls                                     # window positions D-l
        idx = s >> 6
        sh = (s & 63).astype(np.uint64)
        y = (w[idx] >> sh) | ((w[idx + 1] << np.uint64(1)) << (np.uint64(63) - sh))
        d0 = x - y
        d1 = d0 - np.uint64(1)
        mk = masks[1:D]
        hit = ((d0 & mk) == 0) | ((d1 & mk) == 0)
        for l in (ls[hit]).tolist():
            ncand += 1
            r = (u - (u << l)) & mask
            h = r >> D
            assert h != 0, "precision"
            g = v2(h)
            assert D + g < M
            e = g - l
            if e >= t0:
                excess_hist[e] = excess_hist.get(e, 0) + 1
            val = N + e
            if val > best:
                best, arg = val, ("pair", k, l, D + g - l)
        if verbose and k % 5000 == 0:
            print(f"  N={N} k={k} best={best} ncand={ncand} {time.time()-t_start:.0f}s", flush=True)
    # if best excess from pairs < t0 we only know pairs give < N+t0; report that honestly
    return best, arg, dict(ncand=ncand, hist=dict(sorted(excess_hist.items())),
                           collapse_best=collapse_best, t0=t0)


def witness_check(N, arg):
    """Rebuild n from the witness and simulate T literally."""
    kind = arg[0]
    if kind == "pair":
        _, k, l, k1 = arg
        M = N + 192
        u = pow(3, -k, 1 << M)
        D = N - k
        r = (u - (u << l)) & ((1 << M) - 1)
        a = r & ((1 << D) - 1)
    elif kind == "collapse":
        k = arg[1]
        a = pow(3, -k, 1 << (N - k))
    else:
        k, a = N, 1
    n = a * (1 << k) - 1
    assert 0 < n < (1 << N) and n & 1
    return k0k1_direct(n)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "brute":
        NMAX = int(sys.argv[2])
        for N in range(2, NMAX + 1):
            b = brute(N)
            s = slow(N)[0]
            f, arg, st = fast(N, t0=1, verbose=False)
            f3 = fast(N, t0=3, verbose=False)[0]
            print(N, b, s, f, f3, "OK" if b == s == f else "MISMATCH", flush=True)
    elif mode == "slow":
        N = int(sys.argv[2]); t = time.time()
        print(N, slow(N), f"{time.time()-t:.1f}s")
    elif mode == "fast":
        t0 = 3
        for N in map(int, sys.argv[2:]):
            t = time.time()
            B, arg, st = fast(N, t0=t0)
            el = time.time() - t
            print(f"N={N} B={B} (B-N={B-N}) arg={arg} stats={st} {el:.1f}s", flush=True)
            kk = witness_check(N, arg)
            print(f"  witness simulated: k0,l,k1={kk} k0+k1={kk[0]+kk[2]}", flush=True)
