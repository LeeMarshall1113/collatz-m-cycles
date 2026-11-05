import sympy as sp, math, itertools, sys
from mpmath import mp, quad, mpf, log
mp.dps=80
t=sp.symbols('t')
def forms(a,b,c,d,n):
    N=t**(a*n)*(1-t)**(b*n)
    R=N/((1+t)**(c*n+1)*(2+t)**(d*n+1))
    pf=sp.apart(R,t)
    A=sp.Integer(0);B=0;C=0
    for term in sp.Add.make_args(pf):
        num,den=sp.fraction(sp.together(term))
        # identify
        if den==1:
            A+=sp.integrate(term,(t,0,1)); continue
        f=sp.factor_list(den)
        base=[(fa,e) for fa,e in f[1]]
        assert len(base)==1, term
        fa,e=base[0]; coef=num/f[0]
        if e==1:
            if sp.expand(fa-(1+t))==0: B+=coef
            else: C+=coef
        else:
            A+=sp.integrate(term,(t,0,1))
    return sp.nsimplify(A),sp.Integer(B),sp.Integer(C)
def rates(a,b,c,d,ns=(6,10)):
    out=[]
    for n in ns:
        A,B,C=forms(a,b,c,d,n)
        D=sp.denom(A)
        I=mp.quad(lambda x: x**(a*n)*(1-x)**(b*n)/((1+x)**(c*n+1)*(2+x)**(d*n+1)),[0,0.5,1])
        lD=math.log(int(D)); 
        coef=max(abs(int(D*A)),abs(int(D*B)),abs(int(D*C)),1)
        out.append((n,lD/n,-float(log(abs(I)))/n - lD/n, math.log(coef)/n))
    return out
for a,b,c,d in [(1,1,1,1),(1,1,1,0),(1,1,0,1),(2,1,1,1),(1,2,1,1),(2,2,1,1),(1,1,2,1),(1,1,1,2),(2,3,1,1),(3,2,1,1),(1,1,2,2),(2,2,2,1)]:
    try:
        r=rates(a,b,c,d)
        print((a,b,c,d),[(n,round(x,2),round(y,2),round(z,2)) for n,x,y,z in r]); sys.stdout.flush()
    except Exception as e: print((a,b,c,d),'err',e)
