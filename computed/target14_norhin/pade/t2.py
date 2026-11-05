# Type II: Q(s)=D^n[s^n (s^2-1)^n]/n!, pole at s=-3.
# E1 = int_0^1 Q(s)/(s+3) ds = Q(-3)*log(4/3) - P1 ; E2 = int_{-1}^0 Q(s)/(s+3) = Q(-3)*log(3/2) - P2
from fractions import Fraction as F
from math import log, gcd
import sympy as sp
from mpmath import mp, quad, mpf
mp.dps=50
s=sp.symbols('s')
def run(n):
    A=sp.expand(s**n*(s**2-1)**n)
    Q=sp.Poly(sp.diff(A,s,n)/sp.factorial(n),s)
    q=int(Q.eval(-3))
    R,rem=sp.div(sp.Poly(Q.as_expr()-q,s),sp.Poly(s+3,s))
    I=R.integrate()
    P1=F(str(I.eval(1)-I.eval(0))); P2=F(str(I.eval(0)-I.eval(-1)))
    D=sp.ilcm(P1.denominator,P2.denominator)
    e1=quad(lambda x: x**n*(x*x-1)**n/(x+3)**(n+1),[0,1]); e2=quad(lambda x: x**n*(x*x-1)**n/(x+3)**(n+1),[-1,0])
    dn=sp.ilcm(*range(1,2*n+1))
    return q,D,dn,e1,e2
for n in [10,20,30,40,60,80]:
    q,D,dn,e1,e2=run(n)
    E=max(abs(e1),abs(e2))
    print(n,'log q/n=%.3f logD/n=%.3f logd2n/n=%.3f -logE/n=%.3f  alpha_eff=%.3f'%(log(abs(q))/n,log(D)/n,log(dn)/n,-float(mp.log(E))/n,-float(mp.log(E))/n-log(D)/n))
