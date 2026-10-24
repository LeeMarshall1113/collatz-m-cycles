"""Surviving cycle shapes (K, p) for an m-cycle with all elements > 2^71, below the Rhin ceiling.

Own method (not Alick's Farey walk): the m2 = 0 bound Lambda < m/X0 holds for every K, so every
shape satisfies 0 < p - K delta < eta := m/(X0 ln2).  These are lattice points of Z^2 in a thin
strip; writing (K, p) = x (q_n, p_n) + y (q_{n+1}, p_{n+1}) in the basis of two consecutive
convergents (det = +-1) gives x = s (K e_{n+1} - e q_{n+1}), y = s (e q_n - K e_n) with
e = p - K delta, so x, y range over short intervals; all are enumerated and each candidate is then
filtered exactly with the best Theorem-21 bound at its own K (common.survives).

Rhin ceiling (Simons-de Weger Lemma 12 form): Lambda > exp(-13.3 (0.46057 + ln K)).  With m2 = m,
N = floor(K/G(m)) >= K/G - 1, Theorem 21 gives Lambda < m/(2^N - 1) <= m 2^(2 - K/G).
g(K) = (K/G - 2) ln2 - ln m - 13.3 (0.46057 + ln K) is increasing for K > 13.3 G/ln2, so the least
K0 above that with g(K0) >= 0 (checked in interval arithmetic) excludes every K >= K0.
"""
import sys, math
from fractions import Fraction as F
from mpmath import iv
import common as C


def convergents(nmax=80):
    """continued fraction of delta, each partial quotient certified from both ends of the interval"""
    lo, hi = C.DLO, C.DHI
    out = []
    p0, q0, p1, q1 = 0, 1, 1, 0
    for _ in range(nmax):
        a, b = math.floor(lo), math.floor(hi)
        if a != b:
            break
        p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
        out.append((a, p1, q1))
        lo, hi = lo - a, hi - a
        if lo == 0:
            break
        lo, hi = 1 / hi, 1 / lo
    return out


def rhin_ceiling(m):
    Gm = C.G(m)
    ln2 = iv.log(2)

    def g_ok(K):
        g = (iv.mpf(K) / iv.mpf(Gm.numerator) * iv.mpf(Gm.denominator) - 2) * ln2 - iv.log(m) \
            - iv.mpf('13.3') * (iv.mpf('0.46057') + iv.log(K))
        return g.a >= 0
    kmono = math.ceil(F(133, 10) * Gm / C.L2LO * 2)      # beyond this g is increasing (L2LO/2 < ln2 margin)
    lo, hi = kmono, 10 ** 40
    assert g_ok(hi) and not g_ok(lo)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if g_ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def strip_points(eta, Kmax, cv):
    """all (K, p) with 1 <= K < Kmax and 0 < p - K delta < eta (eta a Fraction)"""
    n = max(i for i in range(len(cv) - 1) if cv[i][2] <= Kmax)
    _, pn, qn = cv[n]
    _, pn1, qn1 = cv[n + 1]
    s = qn * pn1 - qn1 * pn
    assert s in (1, -1)
    # e_j = p_j - q_j delta as Fraction intervals
    en = (pn - qn * C.DHI, pn - qn * C.DLO)
    en1 = (pn1 - qn1 * C.DHI, pn1 - qn1 * C.DLO)

    def rng(cs):
        return math.floor(min(cs)) - 1, math.ceil(max(cs)) + 1
    xs = [s * (K * e1 - e * qn1) for K in (0, Kmax) for e in (0, eta) for e1 in en1]
    ys = [s * (e * qn - K * e0) for K in (0, Kmax) for e in (0, eta) for e0 in en]
    x0, x1 = rng(xs)
    y0, y1 = rng(ys)
    out = []
    # e = x e_n + y e_{n+1}: for fixed x, y is confined to an interval (e_{n+1} has a fixed sign)
    en_m, en1_m = (en[0] + en[1]) / 2, (en1[0] + en1[1]) / 2
    pad = 2
    for x in range(x0, x1 + 1):
        a, b = (0 - x * en_m) / en1_m, (eta - x * en_m) / en1_m
        ya, yb = math.floor(min(a, b)) - pad, math.ceil(max(a, b)) + pad
        for y in range(max(y0, ya), min(y1, yb) + 1):
            K = x * qn + y * qn1
            p = x * pn + y * pn1
            if not (1 <= K < Kmax):
                continue
            if p - K * C.DLO > 0 and p - K * C.DHI < eta:
                out.append((K, p))
    return sorted(set(out)), (x1 - x0 + 1) * (y1 - y0 + 1)


def surviving(m):
    cv = convergents()
    Kceil = rhin_ceiling(m)
    eta = F(m, C.X0) / C.L2LO
    pts, nbox = strip_points(eta, Kceil, cv)
    surv = [(K, p) for (K, p) in pts if C.survives(m, K, p)]
    return Kceil, pts, surv, nbox


if __name__ == "__main__":
    cv = convergents()
    for i, (a, p, q) in enumerate(cv[:50]):
        if q > 10 ** 17:
            print("conv", i, "a", a, "q", q)
    for m in map(int, sys.argv[1:]):
        Kceil, pts, surv, nbox = surviving(m)
        print(m, "Kceil %.4e" % Kceil, "strip points", len(pts), "box", nbox, "survivors", len(surv))
        for K, p in surv:
            print("  ", K, p, "%.4e" % K)
