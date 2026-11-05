"""Parameter check for the Gelfond-type effective bound (route 2G of PADE-PLAN.md).
All logs natural. Upper bounds use mu1<=0.69315, mu2<=1.09862; w_max<=(L-1)(mu1+mu2)<=1.79178 L.
Prints, for several K, the parameters and the margin of every inequality (must be > 0),
and the final requirement  K/2^80 > LOSS  (LOSS = log(1/|Lambda|) the method needs)."""
from mpmath import mp, mpf, log, ceil, sqrt, loggamma, exp
mp.dps = 50
mu1 = mpf('0.6931471806'); wfac = mpf('1.79178')
def lnfact(n): return loggamma(n+1)
def params(lnK):
    L = mpf(1000)
    for _ in range(60):
        M = 20*L; N = L*L
        h0 = None
        # Ext(h): (2.0149 M - 16*wfac*L) h > M(lnK - ln mu1) + lnfact(M) + M ln2 + ln(2NC) + ln2,
        # lnC = lnN + M(ln(3L)+lnK) + wfac*L*h0   (Siegel, N >= 2 h0 M)
        a = 2.0149*M - 16*wfac*L
        base = M*(lnK - log(mu1)) + lnfact(M) + M*log(2) + log(2*N) + log(N) + M*(log(3*L)+lnK) + log(2)
        h0 = ceil(base/(a - wfac*L))           # fixed point: a*h0 > base + wfac*L*h0
        Lnew = ceil(sqrt(2*h0*M))+1
        if abs(Lnew-L) < 1: break
        L = Lnew
    M = 20*L; N = L*L
    lnC = log(N) + M*(log(3*L)+lnK) + wfac*L*h0
    ext_margin = (2.0149*M - 16*wfac*L)*h0 - (M*(lnK - log(mu1)) + lnfact(M) + M*log(2) + log(2*N*exp(0)) + lnC + log(2))
    # Final: ln|F|_1 <= lnN + lnC + 20*wfac*L*H - HM ln19 ; need lnN + lnfact(N) + lnVinv + ln|F|_1 < -1
    lnVinv = log(N) + lnfact(N-1) + N*(N-1)/2*log(max(1, wfac*L)) + N*(N-1)/2*L*log(36)
    need = log(N) + lnfact(N) + lnVinv + log(N) + lnC + 1
    H = ceil(need/(M*log(19) - 20*wfac*L))
    fin_margin = H*(M*log(19) - 20*wfac*L) - need
    # LOSS: what log(1/|Lambda|) must exceed: approximation errors at l<H, m<M times interpolation growth
    loss = log(N*M) + lnC + M*log(3.3*L*exp(lnK)) + wfac*L*H + H*M*log(40*H) + need + 10
    return dict(L=L, M=M, N=N, h0=h0, H=H, lnC=lnC, ext_margin=ext_margin, fin_margin=fin_margin, loss=loss)
for e in [60, 80, 100, 200, 1000, 10**4]:
    lnK = e*log(10)
    P = params(lnK)
    target = exp(lnK)/2**80
    print('K=1e%-5d L=%s M=%s h0=%s H=%.3e  ext_margin=%.3e fin_margin=%.3e  LOSS=%.3e  K/2^80=%.3e  ok=%s' % (
        e, int(P['L']), int(P['M']), int(P['h0']), float(P['H']), float(P['ext_margin']), float(P['fin_margin']),
        float(P['loss']), float(target), P['loss'] < target and P['ext_margin']>0 and P['fin_margin']>=0))
