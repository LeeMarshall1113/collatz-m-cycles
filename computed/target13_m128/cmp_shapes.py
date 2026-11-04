"""Compare original fastshapes.box_points (midpoint y-window) with shapes13 (endpoint y-window) on all intervals at m."""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import shapes13 as S
from fractions import Fraction as F
FS, C = S.FS, S.C
if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        t = time.time()
        Kceil = FS.shapes.rhin_ceiling(m)
        iv = FS.merge(FS.intervals(m, Kceil))
        a = b = 0; extra = []
        for Ka, Kb, L in iv:
            eta = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
            o = set(S.ORIG(Ka, Kb, eta)[0]); n = set(S.box_points(Ka, Kb, eta)[0])
            assert o <= n, (Ka, Kb)
            a += len(o); b += len(n); extra += sorted(n - o)[:3]
        print(f"m={m} orig={a} fixed={b} new-only={b - a} {extra[:5]} {time.time() - t:.0f}s", flush=True)
