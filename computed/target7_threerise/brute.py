"""Brute force B_r(N) = max over odd n < 2^N of k_0 + ... + k_{r-1} (first r ascending runs),
by literally iterating T(n) = (3n+1)/2 (n odd), n/2 (n even).  Vectorised over all odd n < 2^N
with numpy int64 (object dtype is not needed: values stay < 2^63 for N <= 24 and r = 3, checked).

usage: python brute.py NMAX            prints N, B2, B3 for N = 2..NMAX
"""
import sys
import numpy as np


def runs(N, r):
    n = np.arange(1, 1 << N, 2, dtype=np.int64)
    tot = np.zeros_like(n)
    x = n.copy()
    for _ in range(r):
        # ascending run: x odd -> (3x+1)/2 while odd
        k = np.zeros_like(n)
        odd = (x & 1) == 1
        while odd.any():
            x = np.where(odd, (3 * x + 1) >> 1, x)
            k += odd
            odd = odd & ((x & 1) == 1)
        tot += k
        assert (x > 0).all() and (x < (1 << 62)).all()
        # descent
        ev = (x & 1) == 0
        while ev.any():
            x = np.where(ev, x >> 1, x)
            ev = (x & 1) == 0
    return tot


if __name__ == "__main__":
    for N in range(2, int(sys.argv[1]) + 1):
        b2 = int(runs(N, 2).max())
        b3 = int(runs(N, 3).max())
        print(N, b2, b3, flush=True)
