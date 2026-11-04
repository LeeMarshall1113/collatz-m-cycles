# For every merged piece and every x the code loops over, check that the rigorous y-range
# (interval endpoints of e_n, e_{n+1}, e' in [elo, ehi]) lies inside the code's [ya, yb].
import sys, math, time
sys.path.insert(0, r'C:\Users\hackathon\Documents\GitHub\collatz-m-cycles-release\computed\target7b_push')
import fastshapes as FS
from fractions import Fraction as F
C = FS.C; CV = FS.CV; EJ = FS.EJ
m = int(sys.argv[1]); t = time.time()
Kc = FS.shapes.rhin_ceiling(m)
iv = FS.merge(FS.intervals(m, Kc))
bad = 0; empty = 0; nx = 0; minmargin = None
for Ka, Kb, L in iv:
    eta = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
    Lk = Kb - Ka; pa = math.floor(Ka * C.DLO)
    ea_lo, ea_hi = pa - Ka * C.DHI, pa - Ka * C.DLO
    elo = -ea_hi; ehi = eta + Kb * (C.DHI - C.DLO) - ea_lo
    best = None
    for n in range(len(CV) - 2):
        qn, qn1 = CV[n][2], CV[n + 1][2]
        e1 = abs(float(EJ[n + 1][0]))
        if e1 == 0: continue
        cost = Lk * e1 + float(ehi - elo) * qn1 + 1
        ycost = min(float(ehi - elo) / e1, Lk / qn1) + 5
        c = cost * ycost
        if best is None or c < best[0]: best = (c, n)
    n = best[1]; en, en1 = EJ[n], EJ[n + 1]
    assert (en1[0] > 0) == (en1[1] > 0)
    xs = [FS_s * 0 for FS_s in []]
    s = CV[n][2] * CV[n + 1][1] - CV[n + 1][2] * CV[n][1]
    xs = [s * (K * e1 - e * CV[n + 1][2]) for K in (0, Lk) for e in (elo, ehi) for e1 in en1]
    x0, x1 = math.floor(min(xs)) - 1, math.ceil(max(xs)) + 1
    en_m, en1_m = (en[0] + en[1]) / 2, (en1[0] + en1[1]) / 2
    for x in range(x0, x1 + 1):
        nx += 1
        a, b = (elo - x * en_m) / en1_m, (ehi - x * en_m) / en1_m
        ya, yb = math.floor(min(a, b)) - 2, math.ceil(max(a, b)) + 2
        rig = [(e - x * a_) / b_ for e in (elo, ehi) for a_ in en for b_ in en1]
        lo, hi = min(rig), max(rig)
        mg = min(lo - ya, yb - hi)
        if minmargin is None or mg < minmargin: minmargin = mg
        if lo < ya or hi > yb:
            # a true point needs 0 < p - K delta < eta with K < Kb; by best approximation,
            # for 1 <= K < q_{j+1}: |p - K delta| >= |e_j|.  Empty piece if eta < min |e_j|.
            jj = max(i for i in range(len(CV)) if CV[i][2] <= Kb)
            assert jj + 1 < len(CV) and CV[jj + 1][2] > Kb
            ej_lo = min(abs(EJ[jj][0]), abs(EJ[jj][1]))
            if eta < ej_lo: empty += 1
            else: bad += 1
print(f"m={m} pieces={len(iv)} x-iterations={nx} bad={bad} (code-window misses, piece provably empty: {empty}) min margin={float(minmargin):.6f} {time.time()-t:.1f}s")
