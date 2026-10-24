"""The chain bound for one shape (K, p) (own implementation of Alick's argument).

Facts used (all [known], formalised in Alick's Lean repo; re-derived by hand where noted):
  (a) Lemma 8: K = sum_t k_t <= sum_{t<m} x_t,  x_t = log2(n_t + 1), n_t the local minima in
      cyclic order from the least element n_0.
  (b) Lemma 20: x_{t+1} <= delta x_t.
  (c) two-step: x_{t+2} <= x_t + (delta - 1)(k_t + k_{t+1}) - 2 + 6/(n_t + 1); with n_t > 2^71
      the last term is <= 2^-S for S <= 68.  If x_t <= N then n_t < 2^N, so k_t + k_{t+1} <= B(N).
  (d) Theorem 21 at the floor X = n_0: n_0 < Ub (common.Ub_cert), so x_0 <= log2 Ub.
Chain (integers in units of 2^-S, all rounding upward):
  Y_0 = ceil(2^S log2 Ub),  Y_{t+1} <= ceil(DU Y_t),
  Y_{t+2} = min(ceil(DU Y_{t+1}), Y_t + ceil((DU-1) B 2^S) - 2^(S+1) + 1)  with B = min B(N) over
  grid points with N 2^S >= Y_t.  By induction x_t <= Y_t 2^-S, so sum Y_t < K 2^S contradicts (a).
"""
import math
from fractions import Fraction as F
from mpmath import iv
from mpmath.libmp import to_rational
import bisect
import common as C

S = 64
SC = 1 << S


def ceilF(x):
    return -((-x.numerator) // x.denominator)


def Y0_of(Ub):
    """ceil(2^S log2 Ub), from an interval upper bound"""
    l = iv.log(iv.mpf(Ub.numerator)) - iv.log(iv.mpf(Ub.denominator))
    v = l / iv.log(2) * SC
    return math.ceil(F(*to_rational(v._mpi_[1])))


class Grid:
    def __init__(self, pairs):
        self.pairs = sorted(pairs)          # (N, B)
        # suffix minima of B so that "min B over N >= y" is a lookup
        self.suf = [0] * len(self.pairs)
        m = None
        for i in range(len(self.pairs) - 1, -1, -1):
            b = self.pairs[i][1]
            m = b if m is None else min(m, b)
            self.suf[i] = m
        self.Ns = [N for N, _ in self.pairs]

    def B_for(self, Y):
        i = bisect.bisect_left(self.Ns, ceilF(F(Y, SC)))
        return None if i == len(self.Ns) else self.suf[i]


def chain(m, Y0, grid):
    G2 = {}
    Ys = [Y0, ceilF(C.DU * Y0)]
    used = []
    while len(Ys) < m:
        Yp, Yc = Ys[-2], Ys[-1]
        a = ceilF(C.DU * Yc)
        B = grid.B_for(Yp)
        if B is not None and Yp >= 2 * SC:
            if B not in G2:
                G2[B] = ceilF((C.DU - 1) * B * SC)
            b = Yp + G2[B] - 2 * SC + 1
            if b < a:
                a = b
                used.append(ceilF(F(Yp, SC)))
        Ys.append(a)
    return Ys[:m], used


def shape_check(m, K, p, grid):
    """returns dict with the certificate and ratio = sum Y / (K 2^S) (< 1 means excluded)"""
    r = C.Ub_cert(m, K, p)
    if r is None:
        return dict(K=K, p=p, ok=False, why="no room")
    Ub, m2, N, M = r
    if Ub <= C.X0:              # n_0 < Ub <= 2^71 + 1 contradicts n_0 > 2^71
        return dict(K=K, p=p, ok=True, small=True, Ub=Ub, m2=m2, ratio=F(0))
    Y0 = Y0_of(F(math.ceil(Ub)))   # n_0 < Ub gives n_0 + 1 <= ceil(Ub), not <= Ub (referee 2)
    Ys, used = chain(m, Y0, grid)
    ratio = F(sum(Ys), K * SC)
    return dict(K=K, p=p, ok=ratio < 1, small=False, Ub=Ub, m2=m2, N=N, M=M, log2Ub=Y0 / SC,
                ratio=ratio, Ys=Ys, used=used, maxN=max(used) if used else 0, top=Ys[-1] / SC)
