"""r-step chain of minima (target 10).  Generalises target7_threerise/chain3.py to any set of r.

r-step bound (target7c PROOFS.md Cor. 2.3, proved there):
  x_{t+r} <= x_t + (delta-1) B_r(N) - r + c_r / ((n_t+1) ln 2),  c_r = 2((4/3)^r - 1),  N >= x_t.
With n_t > 2^71, c_r/((n+1) ln2) < 2^-64 for r <= 13 (c_13/ln2 = 118.6 < 2^7), so in 2^-64 units
  Y_t = min( ceil(DU Y_{t-1}),  min_r  Y_{t-r} + ceil((DU-1) B_r 2^S) - r 2^S + 1 ).
grids: dict r -> chain.Grid (r >= 2).  [The B_r values for r >= 4 used by model.py are SYNTHETIC.]
"""
import os, sys, math
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', 'target7_threerise')))
import chain3 as C3     # noqa: E402
C, CHN = C3.C, C3.CHN
S, SC, ceilF, Grid = C3.S, C3.SC, C3.ceilF, C3.Grid
for r in range(2, 14):
    assert 2 * ((F(4, 3)) ** r - 1) / F(693, 1000) < 2 ** 7          # ln2 > 0.693


def chainr(m, Y0, grids):
    inc = {}
    Ys = [Y0]
    use = {}
    maxN = {}
    rs = sorted(grids)
    while len(Ys) < m:
        t = len(Ys)
        best, how = ceilF(C.DU * Ys[-1]), 1
        for r in rs:
            if t < r:
                break
            B = grids[r].B_for(Ys[t - r])
            if B is None:
                continue
            key = (B, r)
            if key not in inc:
                inc[key] = ceilF((C.DU - 1) * B * SC) - r * SC + 1
            b = Ys[t - r] + inc[key]
            if b < best:
                best, how = b, r
        if how > 1:
            maxN[how] = max(maxN.get(how, 0), ceilF(F(Ys[t - how], SC)))
        use[how] = use.get(how, 0) + 1
        Ys.append(best)
    return Ys, use, maxN


def shape_check(m, K, p, grids):
    r = C.Ub_cert(m, K, p)
    if r is None:
        return dict(K=K, p=p, ok=False, why="no room")
    Ub = r[0]
    if Ub <= C.X0:
        return dict(K=K, p=p, ok=True, small=True, ratio=F(0))
    Y0 = CHN.Y0_of(F(math.ceil(Ub)))
    Ys, use, maxN = chainr(m, Y0, grids)
    ratio = F(sum(Ys), K * SC)
    return dict(K=K, p=p, ok=ratio < 1, small=False, log2Ub=Y0 / SC, ratio=ratio, use=use, maxN=maxN)
