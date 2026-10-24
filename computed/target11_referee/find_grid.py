import json, os, math
import refchain as M
from fractions import Fraction as Fr
T = '../target11_fourrise/'
snap = json.load(open(T + 'b4_grid_snapshot_le852.json'))
ad = list(json.load(open('adapt_HEAD.json')).keys())
K = 27444133206411171953; p = math.ceil(K * M.D_LO)
base = M.load_grids()
for drop in range(0, 15):
    rm = set(ad[len(ad) - drop:]) if drop else set()
    g4 = {int(k): v['B4'] for k, v in snap.items() if k not in rm}
    tabs = dict(base); tabs[4] = M.Table(g4)
    r, _ = M.ratio(127, K, p, tabs)
    r6, _ = M.ratio(126, K, p, tabs)
    print(drop, sorted(map(int, rm)), f"{float(r):.6f} {float(r6):.6f}")
