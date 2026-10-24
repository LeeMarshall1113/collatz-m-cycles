"""Exact three-rise bound B3(N) = max over odd n < 2^N of k0 + k1 + k2 (first three ascending runs
of the Collatz map T).  Derivation: WRITEUP.md section 1.  Summary:

  u_k = (2/3)^k in Z_2,   sigma = (k0, l0, k1, l1) >= 1,  K = k0 + k1,  lam = l0 + l1,
  P2 = K + lam,
  nu(sigma) = -1 + u_k0 (1 - 2^l0) + 2^l0 u_K (1 - 2^l1)       (parity vector sigma 1^inf)
  z_N(x)    = least i >= N with bit i of x set
  B3(N) = max { z_N(nu) - lam : z_N(nu) > P2 }                 (Theorem 1)
  B2(N) = max { z_N(alpha) - l0 : z_N(alpha) > k0 + l0 },  alpha = -1 + u_k0 (1 - 2^l0).

Feasible sigma split by where bit N falls (all exact):
  C : k0 + l0 >= N      l0 forced (= z_N(-1 + u_k0) - k0), then k1, l1, k2 forced.   N items.
  B : k0 + l0 < N <= K + l0     k1 forced (K + l0 = z_N(alpha)), then l1, k2.        ~N^2/2 items
  A : K + l0 < N        k0, l0, k1 free; l1 free (P2 < N) or forced (P2 >= N).
In A, value >= N + t0  <=>  bits [N, N + t0 + lam) of nu are zero  (and z > P2, automatic here).
  A-main: P2 < N + H, found by a 64-bit window join (fast) and verified exactly.
  A-tail: P2 >= N + H forces z_N(nu') >= N + H for nu' = alpha + 2^l0 u_K; found by a join on
          H window bits and then evaluated exactly (l1 forced).
Output of fast(N, t0): every sigma with value >= N + t0 in A, plus all of B and C exactly; so
  B3(N) <= max(N + t0 - 1, best found), with equality when best found >= N + t0 - 1.
"""
import sys, time
import numpy as np
try:
    import gmpy2
    from gmpy2 import mpz

    def scan1(x, N):
        return gmpy2.bit_scan1(x, N)
except ImportError:              # pragma: no cover
    mpz = int

    def scan1(x, N):
        y = x >> N
        return None if y == 0 else N + ((y & -y).bit_length() - 1)

M64 = (1 << 64) - 1


class Ctx:
    """u_k = (2/3)^k mod 2^M for k = 0..kmax"""

    def __init__(self, N, extra=640, kmax=None):
        self.N = N
        self.M = N + extra
        self.mask = (mpz(1) << self.M) - 1
        mod = 1 << self.M
        two_thirds = mpz(2 * pow(3, -1, mod) % mod)
        self.tt = two_thirds
        self.u = [mpz(1)]
        self.extend(kmax if kmax else N + 200)

    def extend(self, k):
        while len(self.u) <= k:
            self.u.append((self.u[-1] * self.tt) & self.mask)

    def U(self, k):
        if k >= len(self.u):
            self.extend(k + 100)
        return self.u[k]

    def z(self, x):
        r = scan1(x & self.mask, self.N)
        if r is None or r >= self.M - 64:
            raise OverflowError("precision")
        return r


def forced_from_alpha(c, k0, l0, alpha):
    """sigma with (k0, l0) and alpha = -1 + u_k0 (1 - 2^l0), when k1 is forced (K + l0 >= N):
    returns (value, sigma) of the unique feasible sigma."""
    zA = c.z(alpha)
    K = zA - l0
    uK = c.U(K)
    nup = (alpha + (uK << l0)) & c.mask
    P2 = c.z(nup)
    lam = P2 - K
    nu = (nup - (uK << lam)) & c.mask
    zz = c.z(nu)
    assert zz > P2
    return zz - lam, (k0, l0, K - k0, lam - l0)


def forced_from_nup(c, k0, l0, K, nup):
    """sigma with (k0, l0, K) and nu' = alpha + 2^l0 u_K, when l1 is forced (P2 >= N)"""
    P2 = c.z(nup)
    lam = P2 - K
    if lam - l0 < 1:
        return None
    nu = (nup - (c.U(K) << lam)) & c.mask
    zz = c.z(nu)
    if zz <= P2:
        return None
    return zz - lam, (k0, l0, K - k0, lam - l0)


def regions_BC(c, alphas=None):
    """exact best over regions B and C.  alphas[(k0,l0)] reused if given."""
    N = c.N
    best, arg = -1, None
    one = mpz(1)
    for k0 in range(1, N + 1):
        uk = c.U(k0)
        # region C: l0 forced
        a0 = (uk - one) & c.mask
        P1 = c.z(a0)
        l0 = P1 - k0
        alpha = (a0 - (uk << l0)) & c.mask
        v, s = forced_from_alpha(c, k0, l0, alpha)
        if v > best:
            best, arg = v, ('C',) + s
        # region B: l0 free with k0 + l0 < N, k1 forced
        for l0 in range(1, N - k0):
            alpha = (a0 - (uk << l0)) & c.mask
            v, s = forced_from_alpha(c, k0, l0, alpha)
            if v > best:
                best, arg = v, ('B',) + s
    return best, arg


def slow(N):
    """B3(N) by enumerating every feasible sigma (region A by all four parameters).  O(N^4)."""
    c = Ctx(N)
    best, arg = regions_BC(c)
    one = mpz(1)
    for k0 in range(1, N):
        uk = c.U(k0)
        for l0 in range(1, N - k0):
            alpha = (uk - one - (uk << l0)) & c.mask
            for K in range(k0 + 1, N - l0):
                uK = c.U(K)
                nup = (alpha + (uK << l0)) & c.mask
                # l1 free: P2 = K + lam < N
                for lam in range(l0 + 1, N - K):
                    nu = (nup - (uK << lam)) & c.mask
                    v = c.z(nu) - lam
                    if v > best:
                        best, arg = v, ('A1', k0, l0, K - k0, lam - l0)
                # l1 forced: P2 >= N
                r = forced_from_nup(c, k0, l0, K, nup)
                if r and r[0] > best:
                    best, arg = r[0], ('A2',) + r[1]
    return best, arg


def b2_slow(N):
    """B2(N) by the same characterisation (for cross-checking against the referee)"""
    c = Ctx(N)
    best = -1
    one = mpz(1)
    for k0 in range(1, N + 1):
        uk = c.U(k0)
        a0 = (uk - one) & c.mask
        P1 = c.z(a0)
        ls = list(range(1, N - k0)) + [P1 - k0]
        for l0 in ls:
            alpha = (a0 - (uk << l0)) & c.mask
            zz = c.z(alpha)
            if zz > k0 + l0:
                best = max(best, zz - l0)
    return best


# ---------------------------------------------------------------- fast region A
def window_table(c, H):
    """Wt[k, p + H] = bits [p, p + 64) of u_k, k = 0..N, p = -H..N  (uint64)"""
    N = c.N
    Wt = np.zeros((N + 1, N + H + 1), dtype=np.uint64)
    nbytes = ((c.M + H + 64) // 64 + 3) * 8
    for k in range(1, N + 1):
        x = int(c.U(k)) << H                      # bit p of u_k is now at p + H
        w = np.frombuffer(x.to_bytes(nbytes, 'little'), dtype=np.uint64)
        pos = np.arange(0, N + H + 1, dtype=np.int64)
        idx = pos >> 6
        sh = (pos & 63).astype(np.uint64)
        lo = w[idx] >> sh
        hi = np.where(sh == 0, np.uint64(0), (w[idx + 1] << ((np.uint64(64) - sh) & np.uint64(63))))
        Wt[k] = lo | hi
    return Wt


def fast(N, t0, H=48, verbose=False, chunkK=None):
    t_start = time.time()
    c = Ctx(N)
    best, arg = regions_BC(c)
    tBC = time.time() - t_start
    Wt = window_table(c, H)
    one = mpz(1)
    found = []                     # (value, sigma) with value >= N + t0
    if best >= N + t0:
        found.append((best, arg))
    nchk = 0
    ntail = 0
    for l0 in range(1, N - 2):
        # k0 in [1, N - l0 - 2], K in [k0 + 1, N - l0 - 1]
        k0s = np.arange(1, N - l0 - 1, dtype=np.int64)
        if len(k0s) == 0:
            break
        alphas = {}
        WA = np.empty(len(k0s), dtype=np.uint64)
        for i, k0 in enumerate(k0s.tolist()):
            uk = c.U(k0)
            al = (uk - one - (uk << l0)) & c.mask
            alphas[k0] = al
            WA[i] = int((al >> N) & M64)
        Ks = np.arange(2, N - l0, dtype=np.int64)
        W1 = Wt[Ks, N - l0 + H]                                   # window of 2^l0 u_K at N
        # ---- tail: z_N(nu') >= N + H, nu' window = WA + W1 + c', c' in {0,1}
        mH = np.uint64((1 << H) - 1)
        keyA = WA & mH
        order = np.argsort(keyA, kind='stable')
        sk = keyA[order]
        for cc in (0, 1):
            tgt = (np.uint64(0) - W1 - np.uint64(cc)) & mH
            lo = np.searchsorted(sk, tgt, 'left')
            hi = np.searchsorted(sk, tgt, 'right')
            for j in np.nonzero(hi > lo)[0].tolist():
                K = int(Ks[j])
                for ii in range(lo[j], hi[j]):
                    k0 = int(k0s[order[ii]])
                    if k0 >= K:
                        continue
                    ntail += 1
                    nup = (alphas[k0] + (c.U(K) << l0)) & c.mask
                    if c.z(nup) < N + H:
                        continue
                    r = forced_from_nup(c, k0, l0, K, nup)
                    if r and r[0] >= N + t0:
                        found.append((r[0], ('Atail',) + r[1]))
        # ---- main: P2 = K + lam < N + H, lam in [l0 + 1, N + H - K - 1]
        T = max(0, min(64, t0 + l0 + 1))
        mT = np.uint64((1 << T) - 1) if T < 64 else np.uint64(M64)
        keyA = WA & mT
        order = np.argsort(keyA, kind='stable')
        sk = keyA[order]
        step = chunkK or max(1, 4_000_000 // (N + H))
        for s0 in range(0, len(Ks), step):
            Kc = Ks[s0:s0 + step]
            W1c = W1[s0:s0 + step]
            nl = (N + H - Kc - 1) - (l0 + 1) + 1                    # number of lam per K
            nl = np.maximum(nl, 0)
            if nl.sum() == 0:
                continue
            Krep = np.repeat(Kc, nl)
            W1rep = np.repeat(W1c, nl)
            start = np.repeat(np.cumsum(nl) - nl, nl)
            lam = (l0 + 1) + (np.arange(len(Krep), dtype=np.int64) - start)
            Q = W1rep - Wt[Krep, N - lam + H]
            tlam = np.clip(t0 + lam, 0, 64)
            mlam = np.where(tlam >= 64, np.uint64(M64),
                            (np.uint64(1) << np.minimum(tlam, 63).astype(np.uint64)) - np.uint64(1))
            for cc in (-1, 0, 1):
                tgt = (np.uint64(0) - Q - np.uint64(cc & M64)) & mT
                lo = np.searchsorted(sk, tgt, 'left')
                hi = np.searchsorted(sk, tgt, 'right')
                hits = np.nonzero(hi > lo)[0]
                for j in hits.tolist():
                    K = int(Krep[j]); lm = int(lam[j])
                    for ii in range(lo[j], hi[j]):
                        k0 = int(k0s[order[ii]])
                        if k0 >= K:
                            continue
                        full = (int(WA[order[ii]]) + int(Q[j]) + cc) & int(mlam[j])
                        if full != 0:
                            continue
                        nchk += 1
                        uK = c.U(K)
                        nu = (alphas[k0] + (uK << l0) - (uK << lm)) & c.mask
                        zz = c.z(nu)
                        if zz > K + lm and zz - lm >= N + t0:
                            found.append((zz - lm, ('A', k0, l0, K - k0, lm - l0)))
        if verbose and l0 % 200 == 0:
            print(f"  N={N} l0={l0} found={len(found)} nchk={nchk} ntail={ntail} "
                  f"{time.time() - t_start:.0f}s", flush=True)
    fb = max(found)[0] if found else -1
    b3 = max(best, fb, N + t0 - 1)
    exact = max(best, fb) >= N + t0 - 1
    return dict(N=N, B3=b3, exact=exact, bestBC=best, argBC=arg, found=sorted(found)[-5:],
                nfound=len(found), allA={(v, s[1:]) for v, s in found if s[0] in ("A", "Atail")}, nchk=nchk, ntail=ntail, t0=t0, H=H,
                secs=time.time() - t_start, secsBC=tBC)


def lower_l11(N):
    """cheap lower bound: sigma with l0 = l1 = 1, P2 < N (value N - 2 + g); O(N^2) exact ops"""
    c = Ctx(N)
    one = mpz(1)
    best, arg = -1, None
    for k0 in range(1, N - 3):
        uk = c.U(k0)
        al = (uk - one - (uk << 1)) & c.mask
        for K in range(k0 + 1, N - 2):
            uK = c.U(K)
            nu = (al + (uK << 1) - (uK << 2)) & c.mask
            v = c.z(nu) - 2
            if v > best:
                best, arg = v, (k0, 1, K - k0, 1)
    return best, arg


def witness(sigma, N):
    """build n < 2^N from sigma's 2-adic nu and simulate T literally; returns (n bits, k0,k1,k2)"""
    k0, l0, k1, l1 = sigma
    c = Ctx(N)
    K = k0 + k1
    nu = (c.U(k0) - 1 - (c.U(k0) << l0) + (c.U(K) << l0) - (c.U(K) << (l0 + l1))) & c.mask
    n = int(nu & ((mpz(1) << N) - 1))
    assert 0 < n < (1 << N) and n & 1
    ks = []
    x = n
    for _ in range(3):
        k = 0
        while x & 1:
            x = (3 * x + 1) >> 1
            k += 1
        ks.append(k)
        while not x & 1:
            x >>= 1
    return n.bit_length(), ks


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "slow":
        for N in map(int, sys.argv[2:]):
            t = time.time()
            print(N, slow(N), b2_slow(N), f"{time.time() - t:.1f}s", flush=True)
    elif mode == "fast":
        t0 = int(sys.argv[2])
        for N in map(int, sys.argv[3:]):
            r = fast(N, t0, verbose=True)
            print(r, flush=True)
    elif mode == "low":
        for N in map(int, sys.argv[2:]):
            t = time.time()
            print(N, lower_l11(N), f"{time.time() - t:.1f}s", flush=True)
