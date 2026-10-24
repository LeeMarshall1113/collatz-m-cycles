"""Shared exact constants and the Theorem-21 bounds (own implementation, target 1a).

Everything load-bearing is a Fraction or an mpmath interval.

  delta = log2 3 in (DLO, DHI)            (100-digit interval from mpmath iv)
  DU    = 1.58496250072116 >= delta        (coarse upper bound used inside geometric sums)
  L2LO  = lower bound for ln 2
  X0    = 2^71 + 1: every element of a nontrivial cycle exceeds 2^71 (Barina: n <= 2^71 reach 1).

Theorem 21, two-element form (Hercher; formalised as lambda_lt_two in Alick's Lean repo):
for a cycle with m local minima, K odd steps, every element >= X (real X > 0), any 1 <= m2 <= m,
and integers N, M >= 1 with  N*m*G(m2) <= m2*K,  M*m*(1+G(m2-1)) <= m2*K   (G(j) = sum_{d<j} DU^d):
      Lambda = p ln2 - K ln3 < (m-m2)/X + 1/(2^N-1) + (m2-1)/(2^M-1).
Remark 7 (m2 = 0 form, ratioIn_of_crude):  Lambda < m/X.
"""
from fractions import Fraction as F
import math
from mpmath import iv, mp

iv.dps = 110
mp.dps = 110
_d = iv.log(3) / iv.log(2)
_l2 = iv.log(2)


from mpmath.libmp import to_rational


def _frac_lo(x):
    return F(*to_rational(x._mpi_[0]))


def _frac_hi(x):
    return F(*to_rational(x._mpi_[1]))


DLO = _frac_lo(_d)
DHI = _frac_hi(_d)
assert DLO < DHI and DHI - DLO < F(1, 10 ** 100)
DU = F(158496250072116, 10 ** 14)
assert DU > DHI
L2LO = _frac_lo(_l2)
X0 = 2 ** 71 + 1
NCAP = 400

_G = {0: F(0)}


def G(j):
    """sum_{d<j} DU^d"""
    if j not in _G:
        s, t = F(0), F(1)
        for _ in range(j):
            s += t
            t *= DU
        _G[j] = s
    return _G[j]


def NM(m, m2, K):
    """the largest admissible (N, M) at K (capped at NCAP), or None"""
    N = math.floor(F(m2 * K) / (m * G(m2)))
    M = math.floor(F(m2 * K) / (m * (1 + G(m2 - 1))))
    N, M = min(N, NCAP), min(M, NCAP)
    if N < 1 or M < 1:
        return None
    return N, M


def tail(m2, N, M):
    return F(1, 2 ** N - 1) + F(m2 - 1, 2 ** M - 1)


def lam_bound(m, K, X=X0):
    """least upper bound on Lambda over m2 (Remark 7 or Theorem 21) at odd-step count K, floor X"""
    best = F(m, X)
    for m2 in range(1, m + 1):
        r = NM(m, m2, K)
        if r is None:
            continue
        b = F(m - m2, X) + tail(m2, *r)
        if b < best:
            best = b
    return best


def survives(m, K, p):
    """False iff the shape (K, p) is refuted by delta < p/K and Lambda < lam_bound:
    Lambda = ln2 (p - K delta), so a cycle needs p - K delta > 0 and p - K delta < lam_bound/ln2."""
    if p <= K * DLO:            # p/K < delta: Lambda < 0 impossible for a cycle
        return False
    return p - K * DHI < lam_bound(m, K) / L2LO


def Ub_cert(m, K, p):
    """bound n0 < Ub for the least element n0, from Theorem 21 with floor X = n0:
    (p - K DHI) L2LO < Lambda < (m-m2)/n0 + tail  =>  n0 < (m-m2)/room.  Returns (Ub, m2, N, M)
    with Ub a Fraction (0 if m2 = m gives a contradiction outright)."""
    lo = (p - K * DHI) * L2LO
    assert lo > 0
    best = None
    for m2 in range(1, m + 1):
        r = NM(m, m2, K)
        if r is None:
            continue
        room = lo - tail(m2, *r)
        if room <= 0:
            continue
        Ub = F(m - m2) / room
        if best is None or Ub < best[0]:
            best = (Ub, m2) + r
    return best
