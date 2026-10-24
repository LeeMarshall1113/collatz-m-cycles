"""Independent shape enumeration (target 7c referee): walk the strip 0 < p - K delta < eta by
successive return times (three-gap / Slater theorem), instead of the repo's lattice-basis box.

For the rotation K -> e(K) = ceil(K delta) - K delta in [0,1), the successive K with e(K) in
(0, eta) differ by g+, g- or g+ + g-, where g+ = least d > 0 with p - d delta in (0, eta) for some
integer p, g- = least d > 0 with p - d delta in (-eta, 0).  The next return from a point with
residue e is the least of these three that lands in (0, eta).

Usage:
  python enum7c.py selftest              compare with brute force for a fat strip
  python enum7c.py m [Kceil]             all survivors (indep.survives) with K < Kceil
"""
import sys, math, time
from fractions import Fraction as F
import indep as I

Q = 360
DQ = math.floor(I.DLO * 2 ** Q)          # DQ / 2^Q <= delta, error < 2^-Q + 1e-100
ONE = 1 << Q


def eQ(K):
    """e(K) = ceil(K delta) - K delta, in units 2^-Q, from DQ (error < K*2^-Q*2, irrelevant)"""
    x = K * DQ
    return (-x) % ONE


def first_pos(eta_q):
    """least d > 0 with e(d) in (0, eta) (e as ceil-residue) -- by semiconvergents"""
    # candidates: all semiconvergent denominators; brute over CF structure
    cands = semis()
    best = None
    for d in cands:
        v = eQ(d)
        if 0 < v < eta_q:
            if best is None or d < best:
                best = d
    return best


def first_neg(eta_q):
    """least d > 0 with p - d delta in (-eta, 0), i.e. 1 - e(d) in (0, eta)"""
    best = None
    for d in semis():
        v = eQ(d)
        if 0 < ONE - v < eta_q and v != 0:
            if best is None or d < best:
                best = d
    return best


_S = None


def semis():
    """all semiconvergent denominators q_{j-1} + i q_j (0 <= i <= a_{j+1}) up to 1e45, from the
    continued fraction of delta certified from both ends of [DLO, DHI]"""
    global _S
    if _S is None:
        lo, hi = I.DLO, I.DHI
        a = []
        for _ in range(95):
            x, y = math.floor(lo), math.floor(hi)
            if x != y:
                break
            a.append(x)
            lo, hi = lo - x, hi - x
            lo, hi = 1 / hi, 1 / lo
        q = [1, 0]          # q_{-2}, q_{-1}
        out = set()
        for j, aj in enumerate(a):
            for i in range(0, aj + 1):
                out.add(q[-2] + i * q[-1])
            q.append(aj * q[-1] + q[-2])
            if q[-1] > 10 ** 45:
                break
        out.discard(0)
        _S = sorted(out)
    return _S


def walk(eta_q, Kmax):
    gp, gn = first_pos(eta_q), first_neg(eta_q)
    fp, fn = eQ(gp), eQ(gn) - ONE          # f(g+) in (0,eta), f(g-) in (-eta,0)
    steps = sorted([(gp, fp), (gn, fn), (gp + gn, fp + fn)])
    out = []
    K, e = gp, fp
    while K < Kmax:
        out.append(K)
        for d, f in steps:
            if 0 < e + f < eta_q:
                K, e = K + d, e + f
                break
        else:
            raise AssertionError("no return")
    return out


def selftest():
    import random
    for eta in (F(1, 1000), F(1, 37), F(3, 10 ** 5)):
        eq = math.floor(eta * ONE)
        Kmax = 300000
        w = walk(eq, Kmax)
        b = [K for K in range(1, Kmax) if 0 < eQ(K) < eq]
        print("eta", eta, "walk", len(w), "brute", len(b), "IDENTICAL" if w == b else "DIFF")


def rhin_check(m, Kc):
    """verify Kceil: g(K) = (K/G - 2) ln2 - ln m - 13.3 (0.46057 + ln K) >= 0 at Kc and g increasing
    beyond 13.3 G / ln2 (G = G_DHI(m) >= G_delta(m), which only weakens N = floor(K/G))."""
    Gm = I.G(m)
    assert Kc > F(133, 10) * Gm / I.LN2LO
    lnK_hi = I.log2_upper(Kc) * I.LN2HI
    lnm_hi = I.log2_upper(m) * I.LN2HI
    g_lo = (F(Kc) / Gm - 2) * I.LN2LO - lnm_hi - F(133, 10) * (F(46057, 100000) + lnK_hi)
    return g_lo >= 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[0] == 'selftest':
        selftest()
        sys.exit()
    m = int(a[0])
    Kc = int(a[1])
    t = time.time()
    print("Rhin ceiling", Kc, "verified:", rhin_check(m, Kc), flush=True)
    eta = F(m, I.X0) / I.LN2LO                     # Remark 7: Lambda < m/X0
    eq = math.ceil(eta * (1 + F(1, 10 ** 30)) * ONE) + 4
    ks = walk(eq, Kc)
    t1 = time.time()
    surv = []
    for K in ks:
        p = math.floor(K * I.DLO) + 1
        assert p == math.floor(K * I.DHI) + 1
        if I.survives(m, K, p):
            surv.append((K, p))
    print(f"m={m} strip points {len(ks)} survivors {len(surv)} walk {t1 - t:.0f}s filter {time.time() - t1:.0f}s", flush=True)
    with open(f"surv7c_m{m}.txt", "w") as f:
        for K, p in surv:
            f.write(f"{K} {p}\n")
