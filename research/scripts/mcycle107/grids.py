"""Test candidate B3 grids for m = 106, 107 (pickles the plans)."""
import sys, os, pickle, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle105'))
sys.argv = [sys.argv[0]]
import chain3 as C
g2 = C.grid103(); b3 = dict(C.b3_all())
PK = os.path.join(HERE, 'plans107.pkl')
if os.path.exists(PK):
    P = pickle.load(open(PK, 'rb'))
else:
    P = {}
    for m in (106, 107):
        t = time.time(); P[m] = C.L.plan_m(m, need_ns=False)
        print(m, "nodes", P[m]['nodes'], "shapes", len(P[m]['certs']), "%.0fs" % (time.time() - t), flush=True)
    pickle.dump(P, open(PK, 'wb'))
def ok(m, Ns):
    g3 = sorted((N, b3[N]) for N in Ns)
    return all(C.shape_ok3(m, g2, g3, c)[0] for c in P[m]['certs'])
U = [73, 79, 122, 128, 203, 213, 325]
print({N: b3[N] for N in U})
for Ns in (U, [73, 79, 128, 203, 213], [79, 122, 203, 325], [79, 122, 203, 213, 325], [73, 79, 122, 203, 325],
           [79, 122, 128, 203, 325], [73, 79, 128, 203, 325]):
    print(Ns, "cost", sum(N**3 for N in Ns) // 10**6, "106", ok(106, Ns), "107", ok(107, Ns), flush=True)
