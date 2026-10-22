import sys, itertools, pickle, os
sys.argv=[sys.argv[0]]
import chain3 as C
g2=C.grid103()
allb3=dict(C.b3_all())
P={m:C.L.plan_m(m,need_ns=False) for m in (104,105)}
pickle.dump(P,open('plans.pkl','wb'))
cands=[N for N in sorted(allb3) if N<=130]
def ok(sub):
    g3=sorted((N,allb3[N]) for N in sub)
    for m in (105,104):
        for c in P[m]['certs']:
            if not C.shape_ok3(m,g2,g3,c)[0]: return False
    return True
# q41-only fast prefilter
q=[c for c in P[105]['certs'] if c['K']==77692117359936589403][0]
def okq(sub):
    g3=sorted((N,allb3[N]) for N in sub)
    return C.shape_ok3(105,g2,g3,q)[0]
best=None
for r in range(1,9):
    for sub in itertools.combinations(cands,r):
        cost=sum(N**3 for N in sub)
        if best and cost>=best[0]: continue
        if okq(sub) and ok(sub):
            best=(cost,sub); print(best,flush=True)
print("best",best)
