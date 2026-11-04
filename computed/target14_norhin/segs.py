import re, sys
from fractions import Fraction as F
R='C:/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/Collatz/'
src=open(R+'HercherAll.lean',encoding='utf8').read()
Kf={}
for m in range(1,92):
    i=src.index('def hercherData%d : Entry :='%m)
    j=src.index('⟩\n',src.index('],',i))
    nums=re.findall(r'\d+',src[src.index('],',i):j+1])
    Kf[m]=int(nums[0])
for m in range(92,112):
    fn = {101:'MCycle101Data',102:'MCycle102Data'}.get(m, 'MCycle%d'%m if m<=100 else 'MCycle%dDef'%m)
    s=open(R+fn+'.lean',encoding='utf8').read()
    Kf[m]=int(re.search(r'Kceil := (\d+)',s).group(1))
s80=open(R+'LogTwoThreeBounds80.lean',encoding='utf8').read()
lo=F(int(re.search(r'def deltaLo80 : ℚ :=\s*(\d+)',s80).group(1)),10**80)
hi=lo+F(1,10**80)
dUp=F(1584962501,10**9)
def geom(m): return sum(dUp**d for d in range(m))
def ceilnat(q): return q.numerator//q.denominator+1
# convergents of delta from lo (exact enough)
from mpmath import mp, log, floor
mp.dps=200
d=log(3)/log(2)
x=d; h0,k0,h1,k1=0,1,1,0; conv=[]
for i in range(80):
    a=int(floor(x)); x=1/(x-a)
    h0,k0,h1,k1=h1,k1,a*h1+h0,a*k1+k0
    conv.append((h1,k1))
K0=int(sys.argv[1]) if len(sys.argv)>1 else 10**30
CAP=1024
# segments: consecutive convergents (P1/Q1, P2/Q2); lower=a/b, upper=c/d
segs=[]
for (P1,Q1),(P2,Q2) in zip(conv,conv[1:]):
    if F(P1,Q1)<F(P2,Q2): a,b,c,dd=P1,Q1,P2,Q2
    else: a,b,c,dd=P2,Q2,P1,Q1
    assert c*b-a*dd==1
    segs.append((a,b,c,dd))
    if b+dd>=K0: break
ok=True
LN2=F(6931471803,10**10)
for (a,b,c,dd) in segs:
    assert F(a,b)<=lo and hi<F(c,dd), (a,b,c,dd)
worst=None
for m in range(1,112):
    Gc=ceilnat(geom(m)); L=Kf[m]
    for (a,b,c,dd) in segs:
        if b+dd<=L: continue
        V=min(L//Gc,CAP)
        val=LN2*L*(F(c,dd)-hi)*2**V
        if not (V>=1 and val>2*m): print('FAIL seg',m,L,V,float(F(c,dd)-hi)); ok=False
        L=b+dd
    V=min(L//Gc,CAP)
    if not (L>=K0 and V>=1 and V*(LN2-F(Gc,2**80))>=2*m): print('FAIL tail',m); ok=False
print('segments',len(segs),'last b+d',segs[-1][1]+segs[-1][3],'ok',ok, 'Gc111',ceilnat(geom(111)), 'min gap', float(min(F(c,dd)-hi for a,b,c,dd in segs)))
print(segs)
