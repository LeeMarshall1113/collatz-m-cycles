"""The three-rise chain (mirror of MCycleChain3.lean) and the choice of the B3 grid points.

usage: python chain3.py m [m ...]
The B2 grid is grid103 (kernel-checked in branch m103); the B3 values are the exact ones of
collatz-loop/research/target7_threerise/grid3_p*.json (the Lean check ThreeRise.AllTriples re-verifies
each one used)."""
import os, sys, json, re, math
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle101_certgen'))
sys.setrecursionlimit(100000)
import gen_mcycle as G
import gen_lean as L

S = L.S
SC = L.SC
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
B3SRC = os.environ.get("B3SRC", "C:/Users/hackathon/Documents/GitHub/collatz-loop/research/target7_threerise")


def grid103():
    src = open(os.path.join(REPO, 'Collatz', 'MCycleGrid103.lean'), encoding='utf-8').read()
    m = re.search(r"def grid103 : List \(ℕ × ℕ\) := \[(.*?)\]\n", src, re.S)
    return [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", m.group(1))]


def b3_all():
    d = {}
    for f in ('grid3_p0.json', 'grid3_p1.json'):
        for k, v in json.load(open(os.path.join(B3SRC, f))).items():
            d[int(k)] = v['B3']
    return sorted(d.items())


def chainG3(B, Y):
    return max(0, Y + (584962501 * B * SC + 999999999) // 1000000000 + 1 - 3 * SC)


def gridB(Y, grid):
    for (N, B) in grid:
        if Y <= N * SC:
            return B, N
    return None, None


def chain3(grid2, grid3, Y0, m, used=None):
    """mirror of chainSeq3"""
    Ys = [Y0, L.chainF(Y0)]
    while len(Ys) < m:
        t = len(Ys)
        Yc, Yp = Ys[-1], Ys[-2]
        v = L.chainNext(grid2, Yp, Yc)
        if t >= 3:
            Ypp = Ys[-3]
            B, N = gridB(Ypp, grid3)
            if B is not None and 3 * SC <= Ypp:
                g = chainG3(B, Ypp)
                if g < v:
                    v = g
                    if used is not None:
                        used.add((N, B))
        Ys.append(v)
    return Ys[:m]


def shape_ok3(m, grid2, grid3, c, used=None):
    if not L.u_ok(m, c['K'], c['P'], c['m2'], c['N'], c['M'], c['Ub']):
        return False, None
    if c['Ub'] <= 2**71 + 1:
        return True, F(0)
    if not (c['Q'] >= 1 and c['Ub'] ** c['Q'] <= 2 ** c['Pe']):
        return False, None
    Ys = chain3(grid2, grid3, L.Y0_of(c), m, used)
    return sum(Ys) < c['K'] * SC, F(sum(Ys), c['K'] * SC)


def choose_grid3(plans, grid2, cand):
    """the smallest set of B3 points that the chains of all plans use, starting from cand"""
    g3 = sorted(cand)
    while True:
        used = set()
        worst = (F(0), None)
        for P in plans:
            for c in P['certs']:
                ok, r = shape_ok3(P['m'], grid2, g3, c, used)
                assert ok, (P['m'], c['K'], float(r) if r is not None else None)
                if r > worst[0]:
                    worst = (r, (P['m'], c['K']))
        new = sorted(used)
        if new == g3:
            return g3, worst
        g3 = new


if __name__ == "__main__":
    ms = list(map(int, sys.argv[1:]))
    g2 = grid103()
    cap = int(os.environ.get("B3CAP", "400"))
    cand = [(N, B) for (N, B) in b3_all() if N <= cap]
    plans = []
    for m in ms:
        P = L.plan_m(m, need_ns=False)
        print(m, "nodes", P['nodes'], "shapes", len(P['certs']), "small",
              sum(c['small'] for c in P['certs']), "fuel", P['fuel'], flush=True)
        plans.append(P)
    g3, worst = choose_grid3(plans, g2, cand)
    print("grid3", g3, "worst %.5f" % float(worst[0]), worst[1])
