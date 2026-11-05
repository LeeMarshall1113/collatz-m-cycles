"""Check the exact inequality fields of GData (Collatz/Gelfond/Core.lean) in log form, high precision.
Parameters, for b = bit length of K (2^(b-1) <= K < 2^b), b >= 333:
  L = 400 b, M = 24 L, N = L^2, h0 = 4 b, J = least j with h0*2^j >= N^2/10, delta = exp(-K/2^80).
Worst case over K in [2^(b-1), 2^b): every term increases with K except delta, which is smallest at K=2^(b-1)+...
we take K := 2^b in all growth terms and K := 2^(b-1) in delta (valid upper bounds)."""
from mpmath import mp, mpf, log, loggamma, ceil
mp.dps = 60
def lf(n): return loggamma(mpf(n)+1)
def check(b):
    L=400*b; M=24*L; N=L*L; h0=4*b
    lnK = b*log(2)                 # K < 2^b
    lndelta = -(mpf(2)**(b-1))/mpf(2)**80
    lnC = log(N) + M*log(3*L) + M*lnK + L*h0*log(6)
    def lneps(h): return log(N)+lnC+log(M)+log(L)+lndelta+M*log(3*L)+L*h*log(6)
    def lnB(h,R): return log(h*M) + h*M*log(2*(R+h))
    def lse(*xs):
        m=max(xs); return m+log(sum(mp.e**(x-m) for x in xs))
    # Ext(h): K^M M! 2^M ((NC e^{29Lh} + eps B(h,16h)) (1/7)^{hM} + eps B(h,2h+1)) + N C M L delta (3LK)^M 6^{2Lh} < (69/100)^M
    def ext(h):
        a = M*lnK + lf(M) + M*log(2)
        t1 = a + lse(log(N)+lnC+29*L*h, lneps(h)+lnB(h,16*h)) - h*M*log(7)
        t2 = a + lneps(h) + lnB(h,2*h+1)
        t3 = log(N)+lnC+log(M)+log(L)+lndelta+M*(log(3*L)+lnK)+2*L*h*log(6)
        return M*log(mpf(69)/100) - lse(t1,t2,t3)     # margin, must be > 0
    J=0
    while h0*2**J < mpf(N)**2/10: J+=1
    margins=[ext(h0*2**j) for j in range(J)]
    H=h0*2**J
    Fmax = lse(lse(log(N)+lnC+36*L*H, lneps(H)+lnB(H,20*H)) - H*M*log(19), lneps(H)+lnB(H,1))
    lhs = log(N)+lf(N-1)+ (mpf(N)*(N-1)/2)*log(mpf(9)/5*L) + L*(mpf(N)*(N-1)/2)*log(36) + lf(N) + Fmax
    return J, min(margins), -lhs
for b in [333, 340, 400, 500, 1000, 3000, 10000]:
    J, mext, mfin = check(b)
    print('b=%5d J=%d  min Ext margin=%.4e  Fin margin=%.4e' % (b, J, float(mext), float(mfin)))
