"""Exact two-rise bound B2(N) = max over odd n < 2^N of k0 + k1: the referee's algorithm
(target1a/referee_tworise/tworise.py, refereed; WRITEUP there: Lemmas 1-3 and the proved 64-bit
filter) with the same mathematics and three engineering changes only:
  * u_k = 3^-k mod 2^M by exact division by 3 (O(M) per k) instead of a full M-bit multiply,
  * 3^k maintained incrementally,
  * the per-k window filter over l = 1..D-1 in numba instead of numpy.
Every kept (k, l) pair is evaluated exactly with gmpy2, as in tworise.fast; the collapse case
(l >= D) and k = N are evaluated exactly.  Exact whenever the best found >= N + t0 - 1 (asserted).
usage: python b2fast.py N [N ...]       (prints B2 and a literally simulated witness)
"""
import sys, time
import numpy as np
from numba import njit
import gmpy2
from gmpy2 import mpz

U64 = np.uint64


@njit(boundscheck=False)
def filt(w, D, t0, out):
    """l in 1..D-1 such that low min(64, l + t0) bits of x - y - b vanish for b = 0 or 1, where
    x = bits [D, D+64) of u and y = bits [D-l, D-l+64) of u (tworise.fast filter)"""
    i = D >> 6
    s = D & 63
    x = (w[i] >> U64(s)) | ((w[i + 1] << U64(1)) << U64(63 - s))
    n = 0
    lsplit = min(D, max(1, 64 - t0))
    for l in range(1, lsplit):
        p = D - l
        i = p >> 6
        s = p & 63
        y = (w[i] >> U64(s)) | ((w[i + 1] << U64(1)) << U64(63 - s))
        mk = (U64(1) << U64(l + t0)) - U64(1)
        d0 = x - y
        if (d0 & mk) == U64(0) or ((d0 - U64(1)) & mk) == U64(0):
            out[n] = l
            n += 1
    for l in range(lsplit, D):
        p = D - l
        i = p >> 6
        s = p & 63
        y = (w[i] >> U64(s)) | ((w[i + 1] << U64(1)) << U64(63 - s))
        d0 = x - y
        if d0 == U64(0) or d0 == U64(1):
            out[n] = l
            n += 1
    return n


def v2(x):
    return gmpy2.bit_scan1(x)


def collapse_fast(w, D, p3_64, M):
    """(l, k1) of the collapse case a0 = u mod 2^D from the words of u = 3^-k mod 2^M:
    3^k a0 - 1 = -2^D 3^k h (mod 2^M), h = u >> D, so l = D + v2(h) and, with h = 2^g h',
    k1 = v2(1 - 3^k h').  Uses 64-bit windows; None if a window is 0 (caller falls back)."""
    def win(p):
        i = p >> 6
        s = p & 63
        lo = int(w[i]) >> s
        if s:
            lo |= (int(w[i + 1]) << (64 - s)) & 0xFFFFFFFFFFFFFFFF
        return lo
    hw = win(D)
    if hw == 0:
        return None
    g = (hw & -hw).bit_length() - 1
    if D + g + 64 > M:
        return None
    hp = win(D + g)
    y = (1 - p3_64 * hp) & 0xFFFFFFFFFFFFFFFF
    if y == 0:
        return None
    return D + g, (y & -y).bit_length() - 1


def b2(N, t0=3, verbose=False, check_collapse=False):
    t_start = time.time()
    M = N + 192
    mod = mpz(1) << M
    mask = mod - 1
    nw = (M + 63) // 64 + 2
    nbytes = nw * 8
    out = np.zeros(N + 2, dtype=np.int64)
    best, arg = -1, None
    u = mpz(1)
    p3 = mpz(1)
    ncand = 0
    for k in range(1, N + 1):
        # u <- u / 3 mod 2^M
        r = (-u) % 3            # u + r 2^M divisible by 3 needs r*2^M = -u mod 3; 2^M mod 3 = (-1)^M
        if M % 2 == 1:
            r = (-r) % 3
        u = gmpy2.divexact(u + r * mod, 3) & mask
        p3 *= 3
        D = N - k
        if k == N:
            x = p3                     # a = 1
            l = v2(x - 1)
            k1 = v2(x - 1 + (mpz(1) << l)) - l
            if k + k1 > best:
                best, arg = k + k1, ("k=N", k, l, k1)
            continue
        w = np.frombuffer(int(u).to_bytes(nbytes, 'little'), dtype=np.uint64)
        cf = collapse_fast(w, D, int(p3 & 0xFFFFFFFFFFFFFFFF), M)
        if cf is None or check_collapse:
            a0 = u & ((mpz(1) << D) - 1)
            x = p3 * a0
            l = v2(x - 1)
            assert l >= D
            k1 = v2(x - 1 + (mpz(1) << l)) - l
            if cf is not None:
                assert cf == (l, k1), (k, cf, l, k1)
        else:
            l, k1 = cf
        if k + k1 > best:
            best, arg = k + k1, ("collapse", k, l, k1)
        if D < 2:
            continue
        n = filt(w, D, t0, out)
        for i in range(n):
            l = int(out[i])
            ncand += 1
            rr = (u - (u << l)) & mask
            h = rr >> D
            assert h != 0
            g = v2(h)
            assert D + g < M
            val = N + g - l
            if val > best:
                best, arg = val, ("pair", k, l, D + g - l)
        if verbose and k % 20000 == 0:
            print(f"  N={N} k={k} best={best} {time.time() - t_start:.0f}s", flush=True)
    assert best >= N + t0 - 1, "filter threshold not reached: not exact"
    return best, arg, ncand, time.time() - t_start


def witness(N, arg):
    """rebuild n and simulate T literally (as tworise.witness_check)"""
    kind = arg[0]
    M = N + 192
    if kind == "pair":
        _, k, l, k1 = arg
        u = pow(3, -k, 1 << M)
        D = N - k
        r = (u - (u << l)) & ((1 << M) - 1)
        a = r & ((1 << D) - 1)
    elif kind == "collapse":
        k = arg[1]
        a = pow(3, -k, 1 << (N - k))
    else:
        k, a = N, 1
    n = mpz(a) * (mpz(1) << k) - 1
    assert 0 < n < (mpz(1) << N) and n & 1
    k0 = 0
    while n & 1:
        n = (3 * n + 1) >> 1
        k0 += 1
    while not n & 1:
        n >>= 1
    k1 = 0
    while n & 1:
        n = (3 * n + 1) >> 1
        k1 += 1
    return k0 + k1


if __name__ == "__main__":
    for N in map(int, sys.argv[1:]):
        B, arg, nc, secs = b2(N, verbose=True)
        ws = witness(N, arg)
        assert ws == B
        print(f"N={N} B2={B} (B2-N={B - N}) arg={arg} ncand={nc} witness_sum={ws} {secs:.1f}s", flush=True)
