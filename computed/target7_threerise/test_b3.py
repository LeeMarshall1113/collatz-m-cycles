"""Set-level check of b3.fast against exhaustive evaluation of every region-A sigma:
the set of region-A sigma with value >= N + t0 found by the window joins (main + tail) must equal
the exhaustive set.  usage: python test_b3.py t0 N...   (H = 2, 6, 48 exercise the tail split)
"""
import sys
import b3
from b3 import Ctx, mpz, forced_from_nup


def slow_set(N, t0):
    c = Ctx(N)
    one = mpz(1)
    out = set()
    for k0 in range(1, N):
        uk = c.U(k0)
        for l0 in range(1, N - k0):
            alpha = (uk - one - (uk << l0)) & c.mask
            for K in range(k0 + 1, N - l0):
                uK = c.U(K)
                nup = (alpha + (uK << l0)) & c.mask
                for lam in range(l0 + 1, N - K):
                    nu = (nup - (uK << lam)) & c.mask
                    v = c.z(nu) - lam
                    if v >= N + t0:
                        out.add((v, (k0, l0, K - k0, lam - l0)))
                r = forced_from_nup(c, k0, l0, K, nup)
                if r and r[0] >= N + t0:
                    out.add(r)
    return out


if __name__ == "__main__":
    t0 = int(sys.argv[1])
    for N in map(int, sys.argv[2:]):
        ref = slow_set(N, t0)
        for H in (2, 6, 48):
            got = b3.fast(N, t0, H=H)['allA']
            print(N, t0, H, len(ref), len(got), "SAME" if got == ref else f"DIFF {sorted(ref ^ got)[:5]}",
                  flush=True)
