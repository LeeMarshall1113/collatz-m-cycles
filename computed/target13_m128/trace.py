"""Trace the r-step chain of the hard shape (exact, same arithmetic as chainr.py) and report, per step t,
which window binds, the looked-up N and B, and Y_t.  Optional extra/synthetic grids for exploration.
usage: python trace.py m [--K K] [--quiet]
Importable: base_grids(), run(m, K, grids) -> (ratio, Ys, how, Ns)."""
import sys, os, math
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'target11_fourrise'))
import run11 as R    # noqa: E402
CR = R.CR; C = CR.C; SC = CR.SC
HARD = 27444133206411171953


def base_grids(b4top=None):
    d2, d3, d4 = R.R7.load_b2(), R.R7.load_b3(), R.load_b4(b4top)
    return {2: d2, 3: d3, 4: d4}


def mk(gd):
    return {r: CR.Grid(list(d.items())) for r, d in gd.items() if d}


def Y0_for(m, K):
    p = math.ceil(K * C.DHI)
    Ub = C.Ub_cert(m, K, p)[0]
    return CR.CHN.Y0_of(F(math.ceil(Ub))), p


def run(m, K, G, Y0=None):
    if Y0 is None:
        Y0, _ = Y0_for(m, K)
    Ys, how, Ns = [Y0], [0], [None]
    rs = sorted(G)
    while len(Ys) < m:
        t = len(Ys)
        best, h, NN = CR.ceilF(C.DU * Ys[-1]), 1, None
        for r in rs:
            if t < r:
                break
            B = G[r].B_for(Ys[t - r])
            if B is None:
                continue
            b = Ys[t - r] + CR.ceilF((C.DU - 1) * B * SC) - r * SC + 1
            if b < best:
                best, h, NN = b, r, (math.ceil(F(Ys[t - r], SC)), B)
        Ys.append(best); how.append(h); Ns.append(NN)
    return F(sum(Ys), K * SC), Ys, how, Ns


if __name__ == "__main__":
    a = sys.argv[1:]
    m = int(a[0])
    K = int(a[a.index('--K') + 1]) if '--K' in a else HARD
    G = mk(base_grids())
    ratio, Ys, how, Ns = run(m, K, G)
    print(f"m={m} K={K} ratio={float(ratio):.6f} Y0={float(Ys[0]/SC):.3f}")
    if '--quiet' not in a:
        for t, (Y, h, N) in enumerate(zip(Ys, how, Ns)):
            print(f"t={t:3d} Y={float(Y/SC):.6g} rule={h} lookup={N}")
