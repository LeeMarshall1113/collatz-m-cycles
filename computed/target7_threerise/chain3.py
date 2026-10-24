"""Chain of minima with two-rise AND three-rise grids (target 7).

Same setting and units as research/target1a/chain/chain.py (integers in units of 2^-S, S = 64,
every operation rounds up).  x_t = log2(n_t + 1), n_0 < Ub the least element (Theorem 21), all
n_t > 2^71.  Bounds used (WRITEUP.md section 2):
  one step   x_{t+1} <= delta x_t                                        (Lemma 20, [known])
  two steps  x_{t+2} <= x_t + (delta-1) B2(N) - 2 + 6/(n_t+1),  N >= x_t   (Alick, [known])
  three steps x_{t+3} <= x_t + (delta-1) B3(N) - 3 + 4/(n_t+1), N >= x_t   (Lemma 3S, proved here)
with 6/(n+1), 4/(n+1) < 2^-68 <= 2^-S.  So
  Y_{t+1} = min( ceil(DU Y_t),
                 Y_{t-1} + ceil((DU-1) B2 2^S) - 2*2^S + 1,      (B2 = least grid B2(N), N 2^S >= Y_{t-1})
                 Y_{t-2} + ceil((DU-1) B3 2^S) - 3*2^S + 1 )     (B3 likewise from Y_{t-2})
and by induction x_t <= Y_t 2^-S; sum_{t<m} Y_t < K 2^S contradicts Lemma 8.
"""
import os, sys, math, bisect
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
CH = os.path.join(HERE, '..', 'target1a', 'chain')
sys.path.insert(0, os.path.abspath(CH))
import common as C            # noqa: E402
import chain as CHN           # noqa: E402

S, SC = CHN.S, CHN.SC
ceilF = CHN.ceilF
Grid = CHN.Grid


def chain3(m, Y0, g2, g3):
    G = {}

    def inc(B, r):
        key = (B, r)
        if key not in G:
            G[key] = ceilF((C.DU - 1) * B * SC) - r * SC + 1
        return G[key]
    Ys = [Y0]
    use = {1: 0, 2: 0, 3: 0}
    maxN = {2: 0, 3: 0}
    while len(Ys) < m:
        t = len(Ys)
        best, how = ceilF(C.DU * Ys[-1]), 1
        if g2 is not None and t >= 2:
            B = g2.B_for(Ys[t - 2])
            if B is not None:
                b = Ys[t - 2] + inc(B, 2)
                if b < best:
                    best, how = b, 2
        if g3 is not None and t >= 3:
            B = g3.B_for(Ys[t - 3])
            if B is not None:
                b = Ys[t - 3] + inc(B, 3)
                if b < best:
                    best, how = b, 3
        if how > 1:
            maxN[how] = max(maxN[how], ceilF(F(Ys[t - how], SC)))
        use[how] += 1
        Ys.append(best)
    return Ys, use, maxN


def shape_check3(m, K, p, g2, g3):
    r = C.Ub_cert(m, K, p)
    if r is None:
        return dict(K=K, p=p, ok=False, why="no room")
    Ub, m2, N, M = r
    if Ub <= C.X0:
        return dict(K=K, p=p, ok=True, small=True, ratio=F(0))
    Y0 = CHN.Y0_of(F(math.ceil(Ub)))
    Ys, use, maxN = chain3(m, Y0, g2, g3)
    ratio = F(sum(Ys), K * SC)
    return dict(K=K, p=p, ok=ratio < 1, small=False, m2=m2, log2Ub=Y0 / SC, ratio=ratio,
                use=use, maxN=maxN, top=Ys[-1] / SC)
