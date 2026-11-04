# Bound the midpoint error in fastshapes.box_points' y-range for every merged piece at m (no enumeration).
import sys, math, time
sys.path.insert(0, r'C:\Users\hackathon\Documents\GitHub\collatz-m-cycles-release\computed\target7b_push')
import fastshapes as FS
C = FS.C; CV = FS.CV; EJ = FS.EJ
from fractions import Fraction as F
m = int(sys.argv[1]); t = time.time()
Kc = FS.shapes.rhin_ceiling(m)
iv = FS.merge(FS.intervals(m, Kc))
w = float(C.DHI - C.DLO)
worst = 0.0; worst_mono = 0.0
prevL = None
for Ka, Kb, L in iv:
    if prevL is not None and L > prevL: worst_mono = max(worst_mono, L / prevL - 1)
    prevL = L
    Lk = Kb - Ka
    etaF = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
    pa = math.floor(Ka * C.DLO); ea_lo, ea_hi = pa - Ka * C.DHI, pa - Ka * C.DLO
    elo = -ea_hi; ehi = etaF + Kb * (C.DHI - C.DLO) - ea_lo
    assert elo >= 0 and ehi < 1 + 1e-9
    best = None
    for n in range(len(CV) - 2):
        qn1 = CV[n + 1][2]; e1 = abs(float(EJ[n + 1][0]))
        if e1 == 0: continue
        cost = Lk * e1 + float(ehi - elo) * qn1 + 1
        ycost = min(float(ehi - elo) / e1, Lk / qn1) + 5
        c = cost * ycost
        if best is None or c < best[0]: best = (c, n)
    n = best[1]; qn = CV[n][2]; qn1 = CV[n + 1][2]
    en = abs(float(EJ[n][0])); en1 = abs(float(EJ[n + 1][0]))
    Xmax = Lk * en1 + 1.01 * qn1 + 2          # |x| <= K'|e_{n+1}| + |e'| q_{n+1}
    Ymax = (1.01 + Xmax * en) / en1 + 2       # |y| <= (|e'| + |x||e_n|)/|e_{n+1}|
    err = (Xmax * qn * w + Ymax * qn1 * w) / en1 * 1.01
    worst = max(worst, err)
print(f"m={m} Kceil={Kc:.4e} pieces={len(iv)} worst y-error bound={worst:.3e} (pad 2) L-increase={worst_mono} {time.time()-t:.1f}s")
