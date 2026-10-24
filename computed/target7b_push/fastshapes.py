"""Fast, exact replacement for shapes.surviving(m) (target1a/chain/shapes.py).

shapes.py enumerates every lattice point of the strip 0 < p - K delta < eta = m/(X0 ln2),
1 <= K < Kceil, and then filters each with common.survives (Theorem 21, exact Fractions).
The strip grows ~1.6x per m (74k points at m = 104); survives() costs ~m Fraction ops per point.

Here: survives(m, K, p) <=> K DLO < p  and  p - K DHI < lam_bound(m, K)/L2LO.  lam_bound(m, K)
depends on K only through (N, M) = NM(m, m2, K) for m2 = 1..m, which are step functions of K with
thresholds K = ceil(j * m G(m2) / m2) (N >= j) and K = ceil(j * m (1 + G(m2-1)) / m2) (M >= j),
computed exactly.  On each interval between consecutive thresholds lam_bound is constant; an
UPPER bound L for it is computed in floats (relative error < 1e-15, inflated by 1e-9).  On that
interval only the lattice points with K DLO < p < K DHI + L / L2LO can survive; they are
enumerated exactly (Fractions, convergent basis chosen per interval) and every one of them is
then passed through the original common.survives.  So the output is exactly
{(K, p): 1 <= K < Kceil, survives(m, K, p)} = shapes.surviving(m)[2]
(survives implies the strip condition, since lam_bound <= m/X0).
"""
import sys, os, math, time, bisect
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
CH = os.path.abspath(os.path.join(HERE, '..', 'target1a', 'chain'))
sys.path.insert(0, CH)
import common as C   # noqa: E402
import shapes        # noqa: E402

CV = shapes.convergents()
# e_j = p_j - q_j delta as Fraction intervals
EJ = [(p - q * C.DHI, p - q * C.DLO) for (_, p, q) in CV]
NCAP = C.NCAP


def thresholds(m, Kceil):
    """events (K, m2, kind) where N (kind 0) or M (kind 1) of NM(m, m2, .) steps up by one"""
    ev = []
    for m2 in range(1, m + 1):
        gN = F(m) * C.G(m2) / m2
        gM = F(m) * (1 + C.G(m2 - 1)) / m2
        for kind, g in ((0, gN), (1, gM)):
            for j in range(1, NCAP + 1):
                K = -((-j * g.numerator) // g.denominator)        # ceil(j g)
                if K >= Kceil:
                    break
                ev.append((K, m2, kind))
    ev.sort()
    return ev


def intervals(m, Kceil):
    """list of (Ka, Kb, Lup): lam_bound(m, K) <= Lup for Ka <= K < Kb (float upper bound)"""
    X0f = float(C.X0)
    N = [0] * (m + 1)
    M = [0] * (m + 1)
    INF = float('inf')
    b = [INF] * (m + 1)
    ev = thresholds(m, Kceil)
    out = []
    Ka = 1
    base = m / X0f
    cur = base

    def bval(m2):
        if N[m2] < 1 or M[m2] < 1:
            return INF
        return (m - m2) / X0f + 1.0 / (2.0 ** N[m2] - 1) + (m2 - 1) / (2.0 ** M[m2] - 1)
    i = 0
    while i < len(ev):
        K = ev[i][0]
        if K > Ka:
            out.append((Ka, K, cur * (1 + 1e-9)))
            Ka = K
        while i < len(ev) and ev[i][0] == K:
            _, m2, kind = ev[i]
            if kind == 0:
                N[m2] += 1
            else:
                M[m2] += 1
            b[m2] = bval(m2)
            i += 1
        cur = min(base, min(b[1:]))
    out.append((Ka, Kceil, cur * (1 + 1e-9)))
    return out


def merge(iv, target=4.0):
    """merge consecutive intervals, using the first (largest: lam_bound is non-increasing in K)
    bound for the union, while the expected number of lattice points (length * L / ln2) <= target"""
    out = []
    Ka, Kb, L = iv[0]
    for a, b, l in iv[1:]:
        assert l <= L * (1 + 1e-6) and a == Kb
        if (b - Ka) * L / 0.693 <= target:
            Kb = b
        else:
            out.append((Ka, Kb, L))
            Ka, Kb, L = a, b, l
    out.append((Ka, Kb, L))
    return out


def box_points(Ka, Kb, eta):
    """all (K, p) with Ka <= K < Kb and K DLO < p < K DHI + eta (eta a Fraction > 0)"""
    Lk = Kb - Ka
    pa = math.floor(Ka * C.DLO)
    # e = p - K delta; anchor e_a = pa - Ka delta in [pa - Ka DHI, pa - Ka DLO] (<= 0)
    ea_lo, ea_hi = pa - Ka * C.DHI, pa - Ka * C.DLO
    # e' = e - e_a must satisfy  -e_a + (K'-dependent slack) ... use a safe superset:
    # 0 < e < eta + K (DHI - DLO)  =>  e' in (-ea_hi, eta + Kb (DHI-DLO) - ea_lo)
    slack = Kb * (C.DHI - C.DLO)
    elo = -ea_hi
    ehi = eta + slack - ea_lo
    # choose basis index n minimising the x-range
    best = None
    for n in range(len(CV) - 2):
        qn, qn1 = CV[n][2], CV[n + 1][2]
        e1 = abs(float(EJ[n + 1][0]))
        if e1 == 0:
            continue
        cost = Lk * e1 + float(ehi - elo) * qn1 + 1
        ycost = min(float(ehi - elo) / e1, Lk / qn1) + 5
        c = cost * ycost
        if best is None or c < best[0]:
            best = (c, n)
    n = best[1]
    _, pn, qn = CV[n]
    _, pn1, qn1 = CV[n + 1]
    s = qn * pn1 - qn1 * pn
    en, en1 = EJ[n], EJ[n + 1]

    def rng(cs):
        return math.floor(min(cs)) - 1, math.ceil(max(cs)) + 1
    xs = [s * (K * e1 - e * qn1) for K in (0, Lk) for e in (elo, ehi) for e1 in en1]
    x0, x1 = rng(xs)
    en_m, en1_m = (en[0] + en[1]) / 2, (en1[0] + en1[1]) / 2
    out = []
    pad = 2
    for x in range(x0, x1 + 1):
        a, b = (elo - x * en_m) / en1_m, (ehi - x * en_m) / en1_m
        ya, yb = math.floor(min(a, b)) - pad, math.ceil(max(a, b)) + pad
        # K' = x qn + y qn1 in [0, Lk)
        ka = -((x * qn) // qn1) - 1
        kb = (Lk - 1 - x * qn) // qn1 + 1
        for y in range(max(ya, ka), min(yb, kb) + 1):
            Kp = x * qn + y * qn1
            if not (0 <= Kp < Lk):
                continue
            K = Ka + Kp
            p = pa + x * pn + y * pn1
            if p - K * C.DLO > 0 and p - K * C.DHI < eta:
                out.append((K, p))
    return out, x1 - x0 + 1


def surviving(m, verbose=False):
    t = time.time()
    Kceil = shapes.rhin_ceiling(m)
    iv = merge(intervals(m, Kceil))
    t1 = time.time()
    cand = []
    iters = 0
    for Ka, Kb, L in iv:
        eta = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
        pts, it = box_points(Ka, Kb, eta)
        iters += it
        cand.extend(pts)
    t2 = time.time()
    cand = sorted(set(cand))
    surv = [(K, p) for (K, p) in cand if 1 <= K < Kceil and C.survives(m, K, p)]
    if verbose:
        print(f"m={m} Kceil={Kceil:.4e} intervals={len(iv)} iters={iters} cand={len(cand)} "
              f"surv={len(surv)}  t_int={t1 - t:.1f}s t_enum={t2 - t1:.1f}s "
              f"t_filter={time.time() - t2:.1f}s", flush=True)
    return Kceil, surv


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'compare':          # validate against shapes.surviving
        for m in map(int, a[1:]):
            t = time.time()
            Kc, surv = surviving(m, verbose=True)
            tf = time.time() - t
            t = time.time()
            Kc0, pts0, surv0, _ = shapes.surviving(m)
            ts = time.time() - t
            print(f"m={m} fast {len(surv)} ({tf:.1f}s)  shapes.py {len(surv0)} strip {len(pts0)} "
                  f"({ts:.1f}s)  Kceil equal {Kc == Kc0}  IDENTICAL {surv == surv0}", flush=True)
    else:
        for m in map(int, a):
            Kc, surv = surviving(m, verbose=True)
