"""Referee (target 7b): own enumeration of surviving shapes (K, p) at m (independent of fastshapes
and shapes.py).

Survival criterion (same statement as common.survives, own code):  p > K D_LO  and
  p - K D_HI < lam(m, K) / LN2_LO,   lam = min( m/X0,  min_{m2} (m-m2)/X0 + 1/(2^N-1) + (m2-1)/(2^M-1) )
with N = min(400, floor(m2 K / (m G(m2)))), M = min(400, floor(m2 K / (m (1 + G(m2-1))))), both >= 1.
Since lam <= m/X0 =: L0, every survivor lies in the strip  K D_LO < p < K D_HI + L0/LN2_LO,
1 <= K < Kceil.  Strip enumeration: Lagrange-reduce the lattice {(K, p)} in the metric scaled by
(1/Kceil, LN2_LO/L0), exact Fractions; then for each first coordinate x (range from the 4 box corners)
the second coordinate y is cut out by the three linear constraints, all exact.
Filter: float lam with exact fallback whenever a floor is within 1e-9 of an integer or the
decision margin is within 1e-7 (relative).
usage: python myshapes.py m [m ...]   -> writes surv_mine_<m>.pkl, compares with surv_fast_<m>.pkl
"""
import sys, os, math, pickle, time
from fractions import Fraction as F
import numpy as np
from mpmath import iv
from mpmath.libmp import to_rational

HERE = os.path.dirname(os.path.abspath(__file__))
iv.dps = 120
_d = iv.log(3) / iv.log(2)
D_LO = F(*map(int, to_rational(_d._mpi_[0])))
D_HI = F(*map(int, to_rational(_d._mpi_[1])))
LN2_LO = F(*map(int, to_rational(iv.log(2)._mpi_[0])))
DU = F(158496250072116, 10 ** 14)
X0 = 2 ** 71 + 1
CAP = 400


def Gs(j):
    s, t = F(0), F(1)
    for _ in range(j):
        s += t
        t *= DU
    return s


def kceil(m):
    """least K0 >= kmono with g(K0) >= 0, g(K) = (K/G(m) - 2) ln2 - ln m - 13.3 (0.46057 + ln K)
    (Rhin form used by the claim; g increasing for K > 13.3 G/ln2)"""
    Gm = Gs(m)
    l2 = iv.log(2)

    def ok(K):
        g = (iv.mpf(K) * iv.mpf(Gm.denominator) / iv.mpf(Gm.numerator) - 2) * l2 - iv.log(m) \
            - iv.mpf('13.3') * (iv.mpf('0.46057') + iv.log(iv.mpf(K)))
        return g.a >= 0
    lo = math.ceil(F(133, 10) * Gm / LN2_LO) + 1
    hi = 10 ** 40
    assert not ok(lo) and ok(hi)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def reduce_basis(Kc, L0):
    """Lagrange reduction of Z^2 basis {(1,0) -> (K=1,p=0), (0,1) -> (K=0,p=1)} in the quadratic form
    Q(K,p) = (K/Kc)^2 + ((p - K D_HI) LN2_LO / L0)^2  (exact)."""
    sK = F(1, Kc)
    se = LN2_LO / L0

    def vec(K, p):
        return (K * sK, (p - K * D_HI) * se)

    def dot(a, b):
        return a[0] * b[0] + a[1] * b[1]
    b1, b2 = (1, 0), (0, 1)
    while True:
        v1, v2 = vec(*b1), vec(*b2)
        if dot(v1, v1) > dot(v2, v2):
            b1, b2 = b2, b1
            v1, v2 = v2, v1
        mu = dot(v1, v2) / dot(v1, v1)
        r = round(mu)
        if r == 0:
            break
        b2 = (b2[0] - r * b1[0], b2[1] - r * b1[1])
    return b1, b2


def strip_points(Kc, L0):
    """all (K, p): 1 <= K < Kc, p - K D_LO > 0, p - K D_HI < L0 / LN2_LO"""
    eta = L0 / LN2_LO
    b1, b2 = reduce_basis(Kc, L0)
    (K1, p1), (K2, p2) = b1, b2
    det = K1 * p2 - K2 * p1
    assert abs(det) == 1
    # (K, p) = x b1 + y b2  ->  x = (K p2 - p K2)/det,  y = (p K1 - K p1)/det
    # box corners in (K, e) with e = p - K D_HI in [-(D_HI-D_LO)Kc, eta]; p = e + K D_HI
    corners = []
    for K in (F(0), F(Kc)):
        for e in (-(D_HI - D_LO) * Kc, eta):
            p = e + K * D_HI
            corners.append(((K * p2 - p * K2) / det, (p * K1 - K * p1) / det))
    x0 = math.floor(min(c[0] for c in corners)) - 1
    x1 = math.ceil(max(c[0] for c in corners)) + 1
    out = []
    for x in range(x0, x1 + 1):
        # K = x K1 + y K2,  p = x p1 + y p2 ; constraints linear in y: a + b y  (op) 0
        lo, hi = -math.inf, math.inf

        def cut(a, b, strict_pos):
            """a + b y > 0 (strict_pos) -> update bounds on integer y"""
            nonlocal lo, hi
            if b == 0:
                if not (a > 0):
                    lo, hi = 1, 0
                return
            r = -a / b
            if b > 0:      # y > r
                lo = max(lo, math.floor(r) + 1)
            else:          # y < r
                hi = min(hi, math.ceil(r) - 1)
        cut(F(x * K1) - F(1, 2), F(K2), True)               # K >= 1
        cut(F(Kc - x * K1) - F(1, 2), F(-K2), True)         # K <= Kc - 1
        cut(x * p1 - x * K1 * D_LO, p2 - K2 * D_LO, True)  # p - K D_LO > 0
        cut(eta - (x * p1 - x * K1 * D_HI), -(p2 - K2 * D_HI), True)   # eta - (p - K D_HI) > 0
        if lo == -math.inf or hi == math.inf:
            raise RuntimeError("unbounded y")
        for y in range(lo, hi + 1):
            K = x * K1 + y * K2
            p = x * p1 + y * p2
            if 1 <= K < Kc and p - K * D_LO > 0 and p - K * D_HI < eta:
                out.append((K, p))
    return sorted(set(out))


def lam_exact(m, K, Gt):
    best = F(m, X0)
    for m2 in range(1, m + 1):
        g, g1 = Gt[m2], 1 + Gt[m2 - 1]
        N = min(CAP, (m2 * K * g.denominator) // (m * g.numerator))
        M = min(CAP, (m2 * K * g1.denominator) // (m * g1.numerator))
        if N < 1 or M < 1:
            continue
        b = F(m - m2, X0) + F(1, 2 ** N - 1) + F(m2 - 1, 2 ** M - 1)
        if b < best:
            best = b
    return best


def survivors(m, pts):
    Gt = [Gs(j) for j in range(m + 1)]
    Ks = np.array([float(K) for K, _ in pts])
    lam = np.full(len(pts), m / float(X0))
    flag = np.zeros(len(pts), dtype=bool)
    for m2 in range(1, m + 1):
        qN = m2 * Ks / (m * float(Gt[m2]))
        qM = m2 * Ks / (m * float(1 + Gt[m2 - 1]))
        for q in (qN, qM):
            fr = q - np.floor(q)
            flag |= (q < CAP + 1) & ((fr < 1e-9) | (fr > 1 - 1e-9))
        N = np.minimum(np.floor(qN), CAP)
        M = np.minimum(np.floor(qM), CAP)
        okk = (N >= 1) & (M >= 1)
        with np.errstate(over='ignore', divide='ignore'):
            b = (m - m2) / float(X0) + 1.0 / (2.0 ** N - 1) + (m2 - 1) / (2.0 ** M - 1)
        b = np.where(okk, b, np.inf)
        lam = np.minimum(lam, b)
    out = []
    nexact = 0
    l2 = float(LN2_LO)
    for i, (K, p) in enumerate(pts):
        if not p - K * D_LO > 0:
            continue
        e = p - K * D_HI
        ef = float(e)
        thr = lam[i] / l2
        if flag[i] or abs(ef - thr) <= 1e-7 * thr:
            nexact += 1
            ok = e < lam_exact(m, K, Gt) / LN2_LO
        else:
            ok = ef < thr
        if ok:
            out.append((K, p))
    return out, nexact


if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        t = time.time()
        Kc = kceil(m)
        pts = strip_points(Kc, F(m, X0))
        t1 = time.time()
        surv, nex = survivors(m, pts)
        print(f"m={m} Kceil={Kc} strip={len(pts)} survivors={len(surv)} exact-fallback={nex} "
              f"strip {t1 - t:.0f}s filter {time.time() - t1:.0f}s", flush=True)
        pickle.dump(dict(m=m, Kceil=Kc, surv=surv), open(os.path.join(HERE, f'surv_mine_{m}.pkl'), 'wb'))
        fp = os.path.join(HERE, f'surv_fast_{m}.pkl')
        if not os.path.exists(fp):
            sys.path.insert(0, os.path.join(HERE, '..', 'target7b_push'))
            import fastshapes
            Kc2, sv = fastshapes.surviving(m)
            pickle.dump(dict(m=m, Kceil=Kc2, surv=sv), open(fp, 'wb'))
        if True:
            d = pickle.load(open(fp, 'rb'))
            A, B = set(surv), set(map(tuple, d['surv']))
            print(f"  vs fastshapes: theirs {len(B)} Kceil equal {d['Kceil'] == Kc}  IDENTICAL {A == B}  "
                  f"mine-theirs {sorted(A - B)[:5]} theirs-mine {sorted(B - A)[:5]}", flush=True)
