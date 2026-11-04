"""fastshapes.box_points with the y-window computed from interval ENDPOINTS (referee finding F1).

Original (target7b_push/fastshapes.py): for each x, y ranged over (e_lo - x e_n)/e_{n+1} .. (e_hi - x e_n)/e_{n+1}
evaluated at the MIDPOINTS of the enclosures e_n, e_{n+1} of p_j - q_j delta, padded by 2.  That is not a
guaranteed superset.  Here: the true e_n lies in [a0, a1], e_{n+1} in [b0, b1] (0 not in [b0, b1], asserted),
and e' = x e_n + y e_{n+1} must lie in [elo, ehi].  For fixed x, y = (e - x a)/b is monotone in e, in a and in
b separately (b of fixed sign), so its extremes over the box occur at corners: y ranges over
[floor(min corners) - 1, ceil(max corners) + 1].  Everything else is the original code, unchanged.
Import this module, then call patch() before using fastshapes / fastchain: it replaces fastshapes.box_points."""
import os, sys, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'target7b_push'))
import fastshapes as FS    # noqa: E402
C, CV, EJ = FS.C, FS.CV, FS.EJ


def box_points(Ka, Kb, eta):
    """all (K, p) with Ka <= K < Kb and K DLO < p < K DHI + eta (eta a Fraction > 0)"""
    Lk = Kb - Ka
    pa = math.floor(Ka * C.DLO)
    slack = Kb * (C.DHI - C.DLO)
    elo = -(pa - Ka * C.DLO)
    ehi = eta + slack - (pa - Ka * C.DHI)
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
    assert (en1[0] > 0) == (en1[1] > 0) and en1[0] != 0 and en1[1] != 0

    def rng(cs):
        return math.floor(min(cs)) - 1, math.ceil(max(cs)) + 1
    xs = [s * (K * e1 - e * qn1) for K in (0, Lk) for e in (elo, ehi) for e1 in en1]
    x0, x1 = rng(xs)
    out = []
    for x in range(x0, x1 + 1):
        ys = [(e - x * a) / b for e in (elo, ehi) for a in en for b in en1]   # exact Fractions, corners
        ya, yb = rng(ys)
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


ORIG = FS.box_points


def patch():
    FS.box_points = box_points
