"""Exact three-rise bound B3(N) in ~N^2 log N (target 7b): a top-window join.

Theorem 1 (target7_threerise/WRITEUP.md, refereed): with u_k = (2/3)^k in Z_2,
  sigma = (k0, l0, k1, l1) >= 1, K = k0 + k1, lam = l0 + l1, P2 = K + lam,
  X = alpha(k0, l0) = -1 + u_k0 (1 - 2^l0),   W(K, l1) = u_K (1 - 2^l1),   nu = X + 2^l0 W,
  B3(N) = max { z_N(nu) - lam : z_N(nu) > P2 }.
value(sigma) >= N + t  <=>  z_N(nu) >= N + t + lam  =>  bits [N + l0, N + l0 + t + l1) of nu are 0.
Those bits are the low t + l1 bits of  P(k0, l0) + Q(K, l1) + c  (mod 2^64), where
  P = bits [N + l0, N + l0 + 64) of X       (two parameters k0, l0)
  Q = bits [N, N + 64) of W                 (two parameters K, l1; = bits [N+l0, ..) of 2^l0 W)
  c in {0, 1} the carry into bit N + l0 of X + 2^l0 W.
So the four-parameter search is a JOIN of two ~N^2/2 lists on a key whose length t + l1 is set by
the Q side: P is sorted by its bit-reversed window (so "low R bits equal" is a contiguous range) and
every Q item looks up its two targets -Q - c.  Expected false matches ~ N^3 2^-t, so with t near
B3 - N the work is ~N^2 (generation, sort, lookups) instead of the N^3 of b3.fast.
P and Q are exact: each borrow of the two-term differences is decided by scanning 64-bit windows
downward until they differ.  Matches pass a second necessary filter (bits [N, N + min(64, t+lam))
of nu zero, both carries allowed) and are then evaluated exactly with gmpy2 (Theorem 1 value and
validity).  Ranges (all valid sigma covered):
  region C (k0 + l0 >= N): l0 forced; N items evaluated exactly (b3.forced_from_alpha).
  otherwise k0 + l0 < N (P list), 2 <= K <= B2(N) (k0 + k1 <= B2(N) for every odd n < 2^N; B2(N)
  from the refereed two-rise checker), 1 <= l1 <= N + 63 - K explicitly; for l1 >= N + 64 - K the
  window Q equals bits [N, N+64) of u_K and P2 >= N, so l1 is forced (P2 = z_N(nu'), WRITEUP 1.3);
  one 'group' item per K covers them and each match is evaluated by b3.forced_from_nup.
Output: every valid sigma with k0 + l0 < N and value >= N + t, plus region C exactly, so
  B3(N) = max(best found) whenever best found >= N + t - 1 (else rerun with smaller t).
"""
import sys, os, time, math
import numpy as np
import numba as nb
from numba import njit

HERE = os.path.dirname(os.path.abspath(__file__))
T7 = os.path.abspath(os.path.join(HERE, '..', 'target7_threerise'))
TW = os.path.abspath(os.path.join(HERE, '..', 'target1a', 'referee_tworise'))
sys.path.insert(0, T7)
sys.path.insert(0, TW)
import b3 as B3M          # noqa: E402
import gmpy2              # noqa: E402
from gmpy2 import mpz     # noqa: E402

U64 = np.uint64
ALL = U64(0xFFFFFFFFFFFFFFFF)


@njit(inline='always')
def ones(n):
    if n >= 64:
        return ALL
    if n <= 0:
        return U64(0)
    return (U64(1) << U64(n)) - U64(1)


@njit(inline='always')
def win(U, k, pos):
    """bits [pos, pos+64) of row k (bits at negative positions are 0)"""
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


@njit(inline='always')
def onesmask(L, q):
    """bits [q, q+64) of 2^L - 1"""
    hi = L - q
    if hi > 64:
        hi = 64
    lo = -q
    if lo < 0:
        lo = 0
    if hi <= lo:
        return U64(0)
    return ones(hi) & ~ones(lo)


@njit(inline='always')
def winA(U, k0, q):
    """bits [q, q+64) of u_k0 - 1 (u_k0 has lowest set bit k0)"""
    return win(U, k0, q) ^ onesmask(k0 + 1, q)


@njit
def borrowX(U, k0, l0, p):
    """[ (u_k0 - 1) mod 2^p < (u_k0 << l0) mod 2^p ]"""
    q = p - 64
    while q > -64:
        a = winA(U, k0, q)
        y = win(U, k0, q - l0)
        if a != y:
            return U64(1) if a < y else U64(0)
        q -= 64
    return U64(0)


@njit
def borrowW(U, K, l1, p):
    """[ u_K mod 2^p < (u_K << l1) mod 2^p ]"""
    q = p - 64
    while q > -64:
        a = win(U, K, q)
        y = win(U, K, q - l1)
        if a != y:
            return U64(1) if a < y else U64(0)
        q -= 64
    return U64(0)


@njit(inline='always')
def winX(U, k0, l0, p):
    return winA(U, k0, p) - win(U, k0, p - l0) - borrowX(U, k0, l0, p)


@njit(inline='always')
def winW(U, K, l1, p):
    return win(U, K, p) - win(U, K, p - l1) - borrowW(U, K, l1, p)


@njit
def winY(U, K, l0, l1, group, q):
    """bits [q, q+64) of 2^l0 W(K, l1) (group: 2^l0 u_K)"""
    if group:
        return win(U, K, q - l0)
    return winW(U, K, l1, q - l0)


@njit
def carryXY(U, k0, l0, K, l1, group, p):
    """[ X mod 2^p + (2^l0 W) mod 2^p >= 2^p ], exactly, by scanning windows downward"""
    q = p - 64
    while q > -64:
        x = winX(U, k0, l0, q)
        y = winY(U, K, l0, l1, group, q)
        if q < 0:                         # only bits >= 0 exist
            mk = ~ones(-q)
            x &= mk
            y &= mk
        sxy = x + y
        if sxy < x:                       # overflow
            return U64(1)
        if sxy != ALL:
            return U64(0)
        q -= 64
    return U64(0)


@njit
def bitrev(x):
    x = ((x >> U64(1)) & U64(0x5555555555555555)) | ((x & U64(0x5555555555555555)) << U64(1))
    x = ((x >> U64(2)) & U64(0x3333333333333333)) | ((x & U64(0x3333333333333333)) << U64(2))
    x = ((x >> U64(4)) & U64(0x0F0F0F0F0F0F0F0F)) | ((x & U64(0x0F0F0F0F0F0F0F0F)) << U64(4))
    x = ((x >> U64(8)) & U64(0x00FF00FF00FF00FF)) | ((x & U64(0x00FF00FF00FF00FF)) << U64(8))
    x = ((x >> U64(16)) & U64(0x0000FFFF0000FFFF)) | ((x & U64(0x0000FFFF0000FFFF)) << U64(16))
    x = (x >> U64(32)) | (x << U64(32))
    return x


@njit
def count_part(U, N, s, j):
    sm = ones(s)
    cnt = 0
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            P = winX(U, k0, l0, N + l0)
            if (P & sm) == U64(j):
                cnt += 1
    return cnt


@njit
def fill_part(U, N, s, j, rev, ids):
    sm = ones(s)
    i = 0
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            P = winX(U, k0, l0, N + l0)
            if (P & sm) == U64(j):
                rev[i] = bitrev(P)
                ids[i] = (k0 << 32) | l0
                i += 1
    return i


@njit
def build_dir(rev, s, r0):
    d = np.zeros((1 << r0) + 1, dtype=np.int64)
    for i in range(len(rev)):
        b = ((rev[i] << U64(s)) >> U64(64 - r0)) if s > 0 else (rev[i] >> U64(64 - r0))
        d[b + 1] += 1
    for b in range(1 << r0):
        d[b + 1] += d[b]
    return d


@njit
def join_part(U, N, Kmax, t, s, j, r0, rev, ids, dirr, out, nout):
    """Q side of the join for partition j.  out rows (k0, l0, K, l1 or -1 for group)."""
    sm = ones(s)
    nmatch = 0
    nfilt = 0
    cap = out.shape[0]
    for K in range(2, Kmax + 1):
        uKN = win(U, K, N)
        l1top = N + 63 - K
        for l1 in range(1, max(l1top, 0) + 2):
            group = l1 == l1top + 1 or l1top < 1
            if group:
                Q = uKN
                R = t + N + 64 - K
            else:
                Q = winW(U, K, l1, N)
                R = t + l1
            if R > 64:
                R = 64
            if R < 0:
                R = 0
            if R < s:
                return -1, nmatch, nfilt          # caller must use smaller s
            mR = ones(R)
            for c in range(2):
                T = (U64(0) - Q - U64(c))
                if (T & sm) != U64(j):
                    continue
                lo = bitrev(T & mR)
                hi = lo | ones(64 - R)
                if s > 0:
                    blo = (lo << U64(s)) >> U64(64 - r0)
                    bhi = (hi << U64(s)) >> U64(64 - r0)
                else:
                    blo = lo >> U64(64 - r0)
                    bhi = hi >> U64(64 - r0)
                for idx in range(dirr[blo], dirr[bhi + 1]):
                    rv = rev[idx]
                    if rv < lo or rv > hi:
                        continue
                    nmatch += 1
                    k0 = ids[idx] >> 32
                    l0 = ids[idx] & 0xFFFFFFFF
                    if k0 >= K:
                        continue
                    # second filter: window of nu (or nu' for group) at N
                    xw = winX(U, k0, l0, N)
                    if group:
                        yw = win(U, K, N - l0)
                        RR = 64
                    else:
                        yw = winW(U, K, l1, N - l0)
                        RR = t + l0 + l1
                        if RR > 64:
                            RR = 64
                    m2 = ones(RR)
                    sw = xw + yw + carryXY(U, k0, l0, K, l1, group, N)
                    if (sw & m2) != U64(0):
                        continue
                    nfilt += 1
                    if nout < cap:
                        out[nout, 0] = k0
                        out[nout, 1] = l0
                        out[nout, 2] = K
                        out[nout, 3] = -1 if group else l1
                    nout += 1
            if group:
                break
    return nout, nmatch, nfilt


class RowCtx:
    """b3.Ctx-compatible view (U(k), z(x), mask, N, M) on the packed rows"""

    def __init__(self, N, M, U):
        self.N, self.M, self.Ur = N, M, U
        self.mask = (mpz(1) << M) - 1
        self.cache = {}

    def U(self, k):
        if k not in self.cache:
            if len(self.cache) > 4096:
                self.cache.clear()
            self.cache[k] = mpz(int.from_bytes(self.Ur[k].tobytes(), 'little')) & self.mask
        return self.cache[k]

    def z(self, x):
        r = gmpy2.bit_scan1(x & self.mask, self.N)
        if r is None or r >= self.M - 64:
            raise OverflowError("precision")
        return r


@njit
def fill_part_pk(U, N, s, j, keys):
    """packed keys: top 32 bits of bitrev(P) | k0 << 16 | l0  (N < 65536); returns count or -1"""
    sm = ones(s)
    i = 0
    cap = keys.shape[0]
    HI = U64(0xFFFFFFFF00000000)
    for k0 in range(1, N - 1):
        for l0 in range(1, N - k0):
            P = winX(U, k0, l0, N + l0)
            if (P & sm) == U64(j):
                if i >= cap:
                    return -1
                keys[i] = (bitrev(P) & HI) | U64((k0 << 16) | l0)
                i += 1
    return i


@njit
def join_part_pk(U, N, Kmax, t, s, j, r0, keys, dirr, out, nout):
    """join_part on packed keys: the top-32-bit range test, then (R > 32) the exact R-bit test
    on the recomputed window P"""
    sm = ones(s)
    nmatch = 0
    nfilt = 0
    cap = out.shape[0]
    for K in range(2, Kmax + 1):
        uKN = win(U, K, N)
        l1top = N + 63 - K
        for l1 in range(1, max(l1top, 0) + 2):
            group = l1 == l1top + 1 or l1top < 1
            if group:
                Q = uKN
                R = t + N + 64 - K
            else:
                Q = winW(U, K, l1, N)
                R = t + l1
            if R > 64:
                R = 64
            if R < 0:
                R = 0
            if R < s:
                return -1, nmatch, nfilt
            mR = ones(R)
            for c in range(2):
                T = (U64(0) - Q - U64(c))
                if (T & sm) != U64(j):
                    continue
                lo = bitrev(T & mR)
                hi = lo | ones(64 - R)
                lo32 = lo >> U64(32)
                hi32 = hi >> U64(32)
                if s > 0:
                    blo = (lo << U64(s)) >> U64(64 - r0)
                    bhi = (hi << U64(s)) >> U64(64 - r0)
                else:
                    blo = lo >> U64(64 - r0)
                    bhi = hi >> U64(64 - r0)
                for idx in range(dirr[blo], dirr[bhi + 1]):
                    kv = keys[idx]
                    rv = kv >> U64(32)
                    if rv < lo32 or rv > hi32:
                        continue
                    k0 = np.int64((kv >> U64(16)) & U64(0xFFFF))
                    l0 = np.int64(kv & U64(0xFFFF))
                    if k0 >= K:
                        continue
                    if R > 32:
                        P = winX(U, k0, l0, N + l0)
                        if ((P + Q + U64(c)) & mR) != U64(0):
                            continue
                    nmatch += 1
                    xw = winX(U, k0, l0, N)
                    if group:
                        yw = win(U, K, N - l0)
                        RR = 64
                    else:
                        yw = winW(U, K, l1, N - l0)
                        RR = t + l0 + l1
                        if RR > 64:
                            RR = 64
                    m2 = ones(RR)
                    sw = xw + yw + carryXY(U, k0, l0, K, l1, group, N)
                    if (sw & m2) != U64(0):
                        continue
                    nfilt += 1
                    if nout < cap:
                        out[nout, 0] = k0
                        out[nout, 1] = l0
                        out[nout, 2] = K
                        out[nout, 3] = -1 if group else l1
                    nout += 1
            if group:
                break
    return nout, nmatch, nfilt


def pack_rows(N, Kmax):
    """U[k] = bits of u_k = (2/3)^k mod 2^M, M = 2N + 256 (rows k = 0..Kmax)"""
    M = 2 * N + 256
    mod = mpz(1) << M
    mask = mod - 1
    nw = M // 64 + 3
    U = np.zeros((Kmax + 1, nw), dtype=np.uint64)
    nb_ = nw * 8
    u = mpz(1)
    for k in range(Kmax + 1):
        U[k] = np.frombuffer(int(u).to_bytes(nb_, 'little'), dtype=np.uint64)
        y = u << 1                                   # u_{k+1} = 2 u_k / 3 mod 2^M
        r = (-y) % 3 if M % 2 == 0 else y % 3        # y + r 2^M = 0 mod 3
        u = gmpy2.divexact(y + r * mod, 3) & mask
    c = RowCtx(N, M, U)
    # spot check against the multiplicative definition
    tt = (2 * pow(3, -1, int(mod))) % int(mod)
    for k in (1, 2, Kmax // 2, Kmax):
        assert int(c.U(k)) == pow(tt, k, int(mod))
    return U, c


def region_C(c):
    N = c.N
    best, arg = -1, None
    one = mpz(1)
    for k0 in range(1, N + 1):
        uk = c.U(k0)
        a0 = (uk - one) & c.mask
        P1 = c.z(a0)
        l0 = P1 - k0
        alpha = (a0 - (uk << l0)) & c.mask
        v, s = B3M.forced_from_alpha(c, k0, l0, alpha)
        if v > best:
            best, arg = v, s
    return best, arg


def exact_value(c, k0, l0, K, l1):
    uk = c.U(k0)
    uK = c.U(K)
    if l1 < 0:                 # group: l1 forced
        alpha = (uk - 1 - (uk << l0)) & c.mask
        nup = (alpha + (uK << l0)) & c.mask
        r = B3M.forced_from_nup(c, k0, l0, K, nup)
        return r
    lam = l0 + l1
    nu = (uk - 1 - (uk << l0) + (uK << l0) - (uK << lam)) & c.mask
    zz = c.z(nu)
    if zz <= K + lam:
        return None
    return zz - lam, (k0, l0, K - k0, l1)


def b2_of(N):
    import tworise
    if N < 500:
        return tworise.slow(N)[0]
    import b2fast                     # same algorithm as tworise.fast (validated equal)
    B, arg, nc, secs = b2fast.b2(N)
    return B


def b3_join(N, t, Kmax=None, s=None, cap=5_000_000, verbose=True, U=None, c=None, packed=None):
    t_start = time.time()
    if Kmax is None:
        Kmax = b2_of(N)
    if U is None:
        U, c = pack_rows(N, Kmax)
    t_pack = time.time() - t_start
    bestC, argC = region_C(c)
    npairs = (N - 2) * (N - 1) // 2
    if packed is None:
        packed = N >= 12000 and N < 65000
    if s is None:
        s = 0
        while (npairs >> s) > (150_000_000 if packed else 25_000_000):
            s += 1
    assert s == 0 or s <= t + 1
    out = np.zeros((cap, 4), dtype=np.int64)
    nout = 0
    nmatch = nfilt = 0
    for j in range(1 << s) if packed else []:
        capk = int((npairs >> s) * 1.02) + 1_000_000
        keys = np.empty(capk, dtype=np.uint64)
        n = fill_part_pk(U, N, s, j, keys)
        assert n >= 0, "partition capacity"
        keys = keys[:n]
        keys.sort()
        r0 = max(1, min(30, int(math.log2(max(n, 2))) - 1))
        dirr = build_dir(keys, s, r0)
        nout, nm, nf = join_part_pk(U, N, Kmax, t, s, j, r0, keys, dirr, out, nout)
        del keys
        if nout < 0:
            raise RuntimeError("R < s")
        nmatch += nm
        nfilt += nf
        if verbose:
            print(f"  N={N} part {j}/{1 << s} n={n} matches={nmatch} filtered={nfilt} "
                  f"{time.time() - t_start:.0f}s", flush=True)
    for j in range(1 << s) if not packed else []:
        n = count_part(U, N, s, j)
        rev = np.empty(n, dtype=np.uint64)
        ids = np.empty(n, dtype=np.int64)
        fill_part(U, N, s, j, rev, ids)
        o = np.argsort(rev)
        rev = rev[o]
        ids = ids[o]
        del o
        r0 = max(1, min(30, int(math.log2(max(n, 2))) - 1))
        dirr = build_dir(rev, s, r0)
        nout, nm, nf = join_part(U, N, Kmax, t, s, j, r0, rev, ids, dirr, out, nout)
        if nout < 0:
            raise RuntimeError("R < s")
        nmatch += nm
        nfilt += nf
        if verbose:
            print(f"  N={N} part {j}/{1 << s} n={n} matches={nmatch} filtered={nfilt} "
                  f"{time.time() - t_start:.0f}s", flush=True)
    if nout > cap:
        raise RuntimeError(f"candidate buffer overflow {nout}; raise t")
    found = []
    for i in range(nout):
        k0, l0, K, l1 = (int(x) for x in out[i])
        r = exact_value(c, k0, l0, K, l1)
        if r and r[0] >= N + t:
            found.append(r)
    found = sorted(set(found))
    fb = found[-1][0] if found else -1
    best = max(bestC, fb)
    exact = best >= N + t - 1
    arg = found[-1][1] if fb >= bestC else argC
    return dict(N=N, B3=best if exact else None, lower=best, exact=exact, t=t, Kmax=Kmax, s=s, packed=packed,
                bestC=bestC, argC=argC, arg=arg, nfound=len(found), ncand=nout,
                nmatch=nmatch, nfilt=nfilt, secs=round(time.time() - t_start, 1),
                secs_pack=round(t_pack, 1), found=found)


def b3_exact(N, t=None, verbose=False):
    """retry with smaller t until exact; witness re-simulated"""
    if t is None:
        t = max(0, int(2 * math.log2(N)) - 7)
    Kmax = b2_of(N)
    U, c = pack_rows(N, Kmax)
    while True:
        r = b3_join(N, t, Kmax=Kmax, verbose=verbose, U=U, c=c)
        if r['exact']:
            break
        t -= 3
    nbits, ks = B3M.witness(r['arg'], N)
    assert sum(ks) == r['B3'] and nbits <= N, (ks, r)
    r['witness_ks'] = ks
    return r


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'set':          # set-level comparison with b3.slow-style exhaustive enumeration
        t = int(a[1])
        for N in map(int, a[2:]):
            r = b3_join(N, t, verbose=False)
            fs = {(v, s) for v, s in r['found']}
            print(N, t, len(fs), r['B3'], r['bestC'], flush=True)
    else:
        t = int(a[0]) if a[0] != 'auto' else None
        for N in map(int, a[1:]):
            r = b3_exact(N, t, verbose=True)
            r.pop('found')
            print(r, flush=True)
