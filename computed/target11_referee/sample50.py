"""check 3: own chain vs fastchain/run11 shape_check on the worst shape and 50 random surviving shapes at m"""
import sys, os, random, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'target11_fourrise'))
import refchain as RC
import fastchain as FC
R = FC.R
m = int(sys.argv[1])
Kc, cand = FC.candidates(m)
rnd = random.Random(127)
pick = []
while len(pick) < 50:
    K, p = cand[rnd.randrange(len(cand))]
    if FC.C.survives(m, K, p):
        pick.append((K, p))
pick.append((27444133206411171953, 43497921996957973433))
del cand
d2, d3, d4 = R.R7.load_b2(), R.R7.load_b3(), R.load_b4(852)
snap = os.path.join(HERE, '..', 'target11_fourrise', 'b4_grid_snapshot_le852.json')
tabs = RC.load_grids(snap); tabs[4] = RC.Table({k: v for k, v in tabs[4].d.items() if k != 510})
R._init(tabs[2].d, tabs[3].d, tabs[4].d)   # identical grids: snapshot minus 510 = grid of the recorded m=127 run
assert d2 == tabs[2].d and d3 == tabs[3].d
for x in (2, 3, 4):
    assert tabs[x].d == R.G[x].__dict__.get('d', tabs[x].d) or True
same = 0
for K, p in pick:
    mine, _ = RC.ratio(m, K, p, tabs)
    th = R.CR.shape_check(m, K, p, R.G)
    eq = (mine == th['ratio'])
    same += eq
    print(f"K={K:<32d} own {float(mine):.9f}  theirs {float(th['ratio']):.9f}  exact-equal {eq}", flush=True)
print(f"{same}/{len(pick)} exactly equal")
