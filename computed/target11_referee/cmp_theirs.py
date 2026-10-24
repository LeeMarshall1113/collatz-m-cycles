import sys, os, math
sys.path.insert(0, os.path.abspath('../target11_fourrise'))
import run11 as R
import refchain as M
d2, d3 = R.R7.load_b2(), R.R7.load_b3(); d4 = R.load_b4(852)
R._init(d2, d3, d4)
K = 27444133206411171953
tabs = M.load_grids(os.path.abspath('../target11_fourrise/b4_grid_snapshot_le852.json'))
print('grid eq', d2 == tabs[2].d, d3 == tabs[3].d, d4 == tabs[4].d, len(d4), len(tabs[4].d))
print(sorted(set(d4.items()) ^ set(tabs[4].d.items())))
for m in (126, 127):
    p = math.ceil(K * M.D_LO)
    r = R.CR.shape_check(m, K, p, R.G)
    print(m, float(r['ratio']), r['use'])
    ub = M.ub_cert(m, K, p); ub2 = R.CR.C.Ub_cert(m, K, p)
    print(' ub equal', ub == ub2[0], M.y0(ub), R.CR.CHN.Y0_of(M.Fr(math.ceil(ub2[0]))))
