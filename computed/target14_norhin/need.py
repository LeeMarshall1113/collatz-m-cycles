from mpmath import mp, mpf, log, nstr
mp.dps=60
d=log(3)/log(2)
for m in [91,100,111,127]:
    G=sum(d**k for k in range(m))
    print(m, nstr(G,6), 'eps=ln2/G=',nstr(log(2)/G,4))
# CF of delta
mp.dps=400
d=log(3)/log(2)
x=d; a=[];
p0,q0,p1,q1=0,1,1,0
qs=[]
for i in range(300):
    ai=int(mp.floor(x)); a.append(ai); x=1/(x-ai)
    p0,q0,p1,q1=p1,q1,ai*p1+p0,ai*q1+q0
    qs.append(q1)
    if q1>10**120: break
print('n partial quotients to 1e120:',len(a),'sum a:',sum(a),'max a:',max(a))
print(a[:40])
