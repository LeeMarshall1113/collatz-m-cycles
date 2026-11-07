from fractions import Fraction as F
from math import log
import sympy as sp, sys
from mpmath import mp, quad
mp.dps=60
s=sp.symbols('s')
def run(a,b,c,m,pole=3):
    # A = s^a (s-1)^b (s+1)^c ; Q = D^m A / m!
    A=sp.expand(s**a*(s-1)**b*(s+1)**c)
    Q=sp.Poly(sp.diff(A,s,m)/sp.factorial(m),s)
    q=int(Q.eval(-pole))
    R,_=sp.div(sp.Poly(Q.as_expr()-q,s),sp.Poly(s+pole,s))
    I=R.integrate()
    P1=F(str(I.eval(1)-I.eval(0))); P2=F(str(I.eval(0)-I.eval(-1)))
    D=sp.ilcm(P1.denominator,P2.denominator)
    f=lambda x: x**a*(x-1)**b*(x+1)**c/(x+pole)**(m+1)
    e1=quad(f,[0,0.5,1]); e2=quad(f,[-1,-0.5,0])
    E=max(abs(e1),abs(e2))
    return log(abs(q)),log(D),-float(mp.log(E)),log(sp.ilcm(*range(1,a+b+c-m+1)))
n=int(sys.argv[1]) if len(sys.argv)>1 else 30
best=[]
for a in [1,1.5,2,2.5,3]:
  for b in [1,1.5,2,2.5,3]:
    A_,B_=int(a*n),int(b*n)
    lq,lD,lE,ld=run(A_,B_,B_,n)
    al=(lE-lD)/n; alcrude=(lE-ld)/n
    print('a=%.1f b=%.1f  logq/n=%.2f logD/n=%.2f logdeg/n=%.2f -logE/n=%.2f  alpha_eff(exactD)=%.3f alpha(lcm)=%.3f'%(a,b,lq/n,lD/n,ld/n,lE/n,al,alcrude)); sys.stdout.flush()
