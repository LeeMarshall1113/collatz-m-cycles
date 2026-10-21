import sys, os, itertools, pickle
G = sys.argv[1]
sys.path.insert(0, G)
import gen_lean as L
ours = {41540: 41554, 45695: 45712, 50265: 50278, 55292: 55308, 60821: 60836, 66903: 66923}
gh = [int(x) for x in open(os.path.join(G, "grid_hi.txt")).read().split(",")]
P = L.plan_m(103, need_ns=False)
print("shapes", len(P['certs']), "small", sum(c['small'] for c in P['certs']), "nodes", P['nodes'], "Kceil", P['Kceil'], flush=True)
base = {N: L.Mbar(N) for N in gh}
base[37763] = 37775
def worst(extra):
    grid = sorted(list(base.items()) + [(N, ours[N]) for N in extra])
    rs = []
    for c in P['certs']:
        if c['small']: continue
        rs.append((sum(L.chainSeq(grid, L.Y0_of(c), 103)) / (c['K'] * L.SC), c['K']))
    rs.sort(reverse=True)
    return rs[0], sum(r[0] >= 1 for r in rs), len(rs)
for k in range(0, 3):
    for ex in itertools.combinations(sorted(ours), k):
        w, f, n = worst(ex)
        print(ex, "worst %.5f K=%d fails %d of %d" % (w[0], w[1], f, n), flush=True)
