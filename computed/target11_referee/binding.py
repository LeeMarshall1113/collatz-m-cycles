import json, math, sys
import refchain as M
T = '../target11_fourrise/'
snap = json.load(open(T + 'b4_grid_snapshot_le852.json'))
K = 27444133206411171953; p = math.ceil(K * M.D_LO)
base = M.load_grids()
def run(m, drop):
    g4 = {int(k): v['B4'] for k, v in snap.items() if int(k) not in drop}
    tabs = dict(base); tabs[4] = M.Table(g4)
    r, tr = M.ratio(m, K, p, tabs)
    b = [(t, c4[3], pt, c4[2]) for t, how, pt, c, _ in tr if how == 4 for c4 in [x for x in c if x[0] == 4]]
    print(m, sorted(drop), f"{float(r):.7f}", [(x[1], x[2], x[3]) for x in b])
    return b
allpts = set()
for m in (126, 127):
    for drop in (set(), {510}, set(range(492, 511))):
        allpts |= {x[2] for x in run(m, drop)}
print('binding grid points (union):', sorted(allpts))
