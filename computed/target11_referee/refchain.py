"""Referee (target 11): own implementation of the all-r chain of minima (Theorem 3.1 of target7c PROOFS.md,
generalised by Cor. 2.3 to r = 2, 3, 4).  Written from the statements, not from chain3/chainr/common.

Units 2^-64.  x_t = log2(n_t + 1).  n_0 < Ub (Theorem 21, X = n_0), so x_0 <= log2 ceil(Ub).
  x_t <= delta x_{t-1}                                         (Lemma 20)
  x_t <= x_{t-r} + (delta - 1) B_r(N) - r + c_r/((n+1) ln 2),  N >= x_{t-r} integer, n > 2^71
c_r/((n+1) ln2) < 2^-64 for r <= 4 (c_4 = 350/81).  delta <= DU.  All rounding upward.
Grids: g_r(N) >= B_r(N) at grid points; lookup = min g_r(N') over N' >= ceil(x).  (Monotonicity of the
true B_r in N is a fact -- n < 2^N is a subset of n < 2^N' -- and is what makes the suffix min valid.)
"""
import os, sys, json, glob, math, bisect
from fractions import Fraction as Fr
import mpmath

mpmath.mp.prec = 600
SH = 64
ONE = 1 << SH
DU = Fr(158496250072116, 10 ** 14)
X0 = 2 ** 71 + 1
NCAP = 400
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))


def _bounds(x, eps=Fr(1, 10 ** 170)):
    q = Fr(mpmath.nstr(x, 190, strip_zeros=False).replace(' ', ''))
    return q - eps, q + eps


D_LO, D_HI = _bounds(mpmath.log(3, 2))
L2_LO, _ = _bounds(mpmath.log(2))
assert D_HI < DU
# certify the delta bounds independently: 2^(a) vs 3^(b) checks via rational approximation
assert 3 ** 10 ** 3 < 2 ** math.ceil(D_HI * 10 ** 3) and 3 ** 10 ** 3 > 2 ** math.floor(D_LO * 10 ** 3)
# ln2 lower bound: ln 2 = sum 1/(k 2^k); partial sums are lower bounds
_s = Fr(0)
for k in range(1, 700):
    _s += Fr(1, k * 2 ** k)
assert L2_LO < _s
GC = {}


def Gsum(j):
    if j not in GC:
        GC[j] = sum((DU ** d for d in range(j)), Fr(0))
    return GC[j]


def ub_cert(m, K, p):
    lo = (p - K * D_HI) * L2_LO
    if lo <= 0:
        return None
    best = None
    for m2 in range(1, m + 1):
        N = min(NCAP, (m2 * K * Gsum(m2).denominator) // (m * Gsum(m2).numerator))
        g1 = 1 + Gsum(m2 - 1)
        M = min(NCAP, (m2 * K * g1.denominator) // (m * g1.numerator))
        if N < 1 or M < 1:
            continue
        room = lo - Fr(1, 2 ** N - 1) - Fr(m2 - 1, 2 ** M - 1)
        if room <= 0:
            continue
        ub = Fr(m - m2) / room
        if best is None or ub < best:
            best = ub
    return best


def cdiv(a, b):
    return -((-a) // b)


def ceilfr(x):
    return cdiv(x.numerator, x.denominator)


def y0(ub):
    """ceil(2^64 log2 ceil(ub)), with a check that the high-precision value is not within 1e-100 of an integer"""
    c = ceilfr(ub)
    v = mpmath.log(c, 2) * ONE
    f = mpmath.floor(v)
    assert v - f > mpmath.mpf(10) ** -100 and f + 1 - v > mpmath.mpf(10) ** -100
    return int(f) + 1


class Table:
    def __init__(self, d):
        self.N = sorted(d)
        self.suf = [0] * len(self.N)
        self.arg = [0] * len(self.N)
        cur, ca = None, None
        for i in range(len(self.N) - 1, -1, -1):
            b = d[self.N[i]]
            if cur is None or b <= cur:
                cur, ca = b, self.N[i]
            self.suf[i] = cur
            self.arg[i] = ca
        self.d = d

    def look(self, Y):
        """(value, grid point giving it) for min over N >= ceil(Y / 2^64)"""
        n = cdiv(Y, ONE)
        i = bisect.bisect_left(self.N, n)
        if i == len(self.N):
            return None, None
        return self.suf[i], self.arg[i]


def chain(m, Y0, tabs, log=False):
    Y = [Y0]
    inc = {}
    trace = []
    while len(Y) < m:
        t = len(Y)
        a = DU * Y[-1]
        best, how, pt = cdiv(a.numerator, a.denominator), 1, None
        cands = [(1, None, None, None, best)]
        for r in sorted(tabs):
            if t < r:
                continue
            B, Np = tabs[r].look(Y[t - r])
            if B is None:
                continue
            key = (r, B)
            if key not in inc:
                q = (DU - 1) * B * ONE
                inc[key] = cdiv(q.numerator, q.denominator) - r * ONE + 1
            v = Y[t - r] + inc[key]
            cands.append((r, Np, B, cdiv(Y[t - r], ONE), v))
            if v < best:
                best, how, pt = v, r, Np
        trace.append((t, how, pt, cands, best))
        Y.append(best)
    return Y, trace


def ratio(m, K, p, tabs):
    ub = ub_cert(m, K, p)
    if ub is None:
        return None, None
    if ub <= X0:
        return Fr(0), None
    Y, tr = chain(m, y0(ub), tabs)
    return Fr(sum(Y), K * ONE), tr


def load_grids(b4file=None):
    j = lambda f: json.load(open(f))
    g2 = {int(k): v for k, v in j(os.path.join(ROOT, 'target1a/chain/grid_own.json')).items()}
    g2.update({int(k): v for k, v in j(os.path.join(ROOT, 'target7_threerise/b2_extra.json')).items()})
    for f in glob.glob(os.path.join(ROOT, 'target7b_push/b2_new*.json')):
        for k, v in j(f).items():
            g2[int(k)] = v['B2'] if isinstance(v, dict) else v
    g3 = {}
    for f in glob.glob(os.path.join(ROOT, 'target7_threerise/grid3*.json')) + glob.glob(os.path.join(ROOT, 'target7b_push/b3_new*.json')):
        for k, v in j(f).items():
            g3[int(k)] = v['B3'] if isinstance(v, dict) else v
    tabs = {2: Table(g2), 3: Table(g3)}
    if b4file:
        g4 = {int(k): v['B4'] for k, v in j(b4file).items()}
        tabs[4] = Table(g4)
    return tabs


if __name__ == "__main__":
    snap = os.path.join(ROOT, 'target11_fourrise/b4_grid_snapshot_le852.json')
    tabs = load_grids(snap)
    K = 27444133206411171953
    for m in map(int, sys.argv[1:]):
        p = math.ceil(K * D_LO)
        r, tr = ratio(m, K, p, tabs)
        use = {}
        for t, how, pt, c, b in tr:
            use[how] = use.get(how, 0) + 1
        print(f"m={m} K={K} p={p} ratio={float(r):.7f} exact={r} use={use}")
        for t, how, pt, c, b in tr:
            if how == 4:
                c4 = [x for x in c if x[0] == 4][0]
                alt = min(x[4] for x in c if x[0] != 4)
                print(f"  t={t} 4-step binding: ceil(x_(t-4))={c4[3]} grid N*={pt} B4={c4[2]}  "
                      f"margin over next-best (2^-64 units) = {alt - b}")
