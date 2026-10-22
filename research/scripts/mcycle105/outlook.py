import sys, itertools
sys.argv=['x']
import chain3 as C
g2=C.grid103(); b3=dict(C.b3_all())
for m in (106,107):
    P=C.L.plan_m(m,need_ns=False)
    print(m,"nodes",P['nodes'],"shapes",len(P['certs']),flush=True)
    q=max(P['certs'],key=lambda c:0 if c['small'] else C.shape_ok3(m,g2,[(79,88),(122,135)],c)[1])
    cands=[N for N in sorted(b3) if N<=400]
    best=None
    for r in range(1,6):
        for sub in itertools.combinations(cands,r):
            cost=sum(N**3 for N in sub)
            if best and cost>=best[0]: continue
            g3=sorted((N,b3[N]) for N in sub)
            if not C.shape_ok3(m,g2,g3,q)[0]: continue
            if all(C.shape_ok3(m,g2,g3,c)[0] for c in P['certs']):
                best=(cost,sub)
        if best: print(" r",r,best,flush=True)
    print(m,"best",best,flush=True)
