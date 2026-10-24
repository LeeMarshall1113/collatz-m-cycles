"""Independent (target 7c referee) exact re-implementation of the m-cycle chain certificate.

Nothing here imports repo code.  All arithmetic is exact (Fraction / int); no floats are used in
any load-bearing comparison.

Constants: ln2 = 2 atanh(1/3), ln(3/2) = 2 atanh(1/5), with rigorous tail bounds, so
LN2LO <= ln2 <= LN2HI, LN3LO <= ln3 <= LN3HI, DLO <= delta = ln3/ln2 <= DHI.

Theorem 21 (Hercher, two-element form; Alick's theorem21_two with the real delta in windowExp):
for a cycle with m local minima, K odd steps, period p, all elements >= X, 1 <= m2 <= m and any
integers 1 <= N <= v = m2 K / (m G(m2)), 1 <= M <= tau = m2 K / (m (1 + G(m2-1))),
G(j) = sum_{d<j} delta^d:
    Lambda = p ln2 - K ln3 < (m-m2)/X + 1/(2^N-1) + (m2-1)/(2^M-1).
We take G with DHI (>= delta) so our N, M are admissible.

Chain (x_t = log2(n_t+1), n_0 the least element, all n_t > 2^71):
  x_{t+1} <= delta x_t
  x_{t+2} <= x_t + (delta-1)(k_t+k_{t+1}) - 2 + 6/(n_t+1)      (k_t+k_{t+1} <= B2(N) if x_t <= N)
  x_{t+3} <= x_t + (delta-1)(k_t+k_{t+1}+k_{t+2}) - 3 + 4/(n_t+1)   (<= B3(N) if x_t <= N)
  sum_{t<m} x_t >= sum k_t = K.
"""
from fractions import Fraction as F
import math, json, glob, os, bisect


def atanh_bounds(x, terms):
    """x = Fraction in (0,1/2]; returns (lo, hi) for atanh(x) = sum x^(2j+1)/(2j+1)"""
    s = F(0)
    for j in range(terms):
        s += x ** (2 * j + 1) / (2 * j + 1)
    j = terms
    tail = x ** (2 * j + 1) / (2 * j + 1) / (1 - x * x)
    return s, s + tail


_a3 = atanh_bounds(F(1, 3), 110)
_a5 = atanh_bounds(F(1, 5), 80)
LN2LO, LN2HI = 2 * _a3[0], 2 * _a3[1]
LN3LO, LN3HI = LN2LO + 2 * _a5[0], LN2HI + 2 * _a5[1]
assert LN2HI - LN2LO < F(1, 10 ** 100) and LN3HI - LN3LO < F(1, 10 ** 100)
# round outward to denominators 2^400 to keep fractions small
P = 400


def _down(x):
    return F(math.floor(x * 2 ** P), 2 ** P)


def _up(x):
    return F(-((-x.numerator * 2 ** P) // x.denominator), 2 ** P)


LN2LO, LN2HI, LN3LO, LN3HI = _down(LN2LO), _up(LN2HI), _down(LN3LO), _up(LN3HI)
DLO, DHI = _down(LN3LO / LN2HI), _up(LN3HI / LN2LO)
assert DLO < DHI and DHI - DLO < F(1, 10 ** 100)
X0 = 2 ** 71 + 1          # Barina: every n <= 2^71 reaches 1, so cycle elements >= 2^71 + 1

_G = {}


def G(j):
    if j not in _G:
        _G[j] = sum((DHI ** d for d in range(j)), F(0))
    return _G[j]


NCAP = 600


def thm21_Ub(m, K, p):
    """min over m2 of (m-m2)/(Lambda_lo - tail): n0 < Ub.  Returns (Ub, m2) or ('contra', m2) when
    m2 = m already contradicts, or None if no m2 has room."""
    lam_lo = p * LN2LO - K * LN3HI
    if lam_lo <= 0:
        return None
    best = None
    for m2 in range(1, m + 1):
        N = min(NCAP, math.floor(F(m2 * K) / (m * G(m2))))
        M = min(NCAP, math.floor(F(m2 * K) / (m * (1 + G(m2 - 1)))))
        if N < 1 or M < 1:
            continue
        tail = F(1, 2 ** N - 1) + F(m2 - 1, 2 ** M - 1)
        room = lam_lo - tail
        if room <= 0:
            continue
        if m2 == m:
            return ('contra', m2)
        Ub = F(m - m2) / room
        if best is None or Ub < best[0]:
            best = (Ub, m2)
    return best


def survives(m, K, p):
    """independent Theorem-21 filter at floor X0: can (K, p) be the shape of an m-cycle with all
    elements >= X0?  Lambda in (p LN2LO - K LN3HI, p LN2HI - K LN3LO)."""
    lam_hi = p * LN2HI - K * LN3LO
    if lam_hi <= 0:
        return False
    lam_lo = p * LN2LO - K * LN3HI
    if lam_lo >= F(m, X0):
        return False
    for m2 in range(m, 0, -1):         # any single admissible m2 with bound <= lam_lo refutes
        N = min(NCAP, math.floor(F(m2 * K) / (m * G(m2))))
        M = min(NCAP, math.floor(F(m2 * K) / (m * (1 + G(m2 - 1)))))
        if N < 1 or M < 1:
            continue
        b = F(m - m2, X0) + F(1, 2 ** N - 1) + F(m2 - 1, 2 ** M - 1)
        if lam_lo >= b:
            return False
    return True


def log2_upper(U):
    """rational upper bound for log2(U), U a positive integer, error < 2^-150"""
    e = U.bit_length() - 1
    y = F(U, 2 ** e)              # in [1, 2)
    if y == 1:
        return F(e)
    z = (y - 1) / (y + 1)         # ln y = 2 atanh z, z < 1/3
    lo, hi = atanh_bounds(z, 120)
    return e + 2 * hi / LN2LO


R = 200                            # chain values rounded up to multiples of 2^-R


def rup(x):
    return F(-((-x.numerator * 2 ** R) // x.denominator), 2 ** R)


class Grid:
    def __init__(self, d):
        self.Ns = sorted(d)
        self.suf = [0] * len(self.Ns)
        cur = None
        for i in range(len(self.Ns) - 1, -1, -1):
            b = d[self.Ns[i]]
            cur = b if cur is None else min(cur, b)
            self.suf[i] = cur

    def lookup(self, x):
        """(N, B): least B over grid points N >= x (x real upper bound of log2(n+1))"""
        need = math.ceil(x)
        i = bisect.bisect_left(self.Ns, need)
        if i == len(self.Ns):
            return None
        return self.Ns[i], self.suf[i]


EPS2 = F(6, 2 ** 71)
EPS3 = F(4, 2 ** 71)


def chain(m, K, p, g2, g3, record=False):
    r = thm21_Ub(m, K, p)
    if r is None:
        return dict(ok=False, why='no room')
    if r[0] == 'contra':
        return dict(ok=True, why='m2=m contradiction', ratio=F(0))
    Ub, m2 = r
    if Ub <= X0:
        return dict(ok=True, why='Ub<=X0', ratio=F(0))
    U = math.ceil(Ub)              # n0 + 1 <= U
    out = chain_x0(m, rup(log2_upper(U)), g2, g3, record)
    out.update(ok=out['S'] < K, ratio=out['S'] / K, Ub=Ub, m2=m2)
    return out


def chain_x0(m, x0, g2, g3, record=False):
    """the chain from an upper bound x0 >= log2(n0+1); returns S = sum of the m bounds.
    S is nondecreasing in x0 (each candidate is nondecreasing in earlier values; the grid
    lookup takes a suffix minimum over N >= ceil(x), nondecreasing in x)."""
    X = [x0]
    used = []
    while len(X) < m:
        t = len(X)
        best, how, info = rup(DHI * X[t - 1]), 1, None
        if t >= 2 and g2 is not None:
            q = g2.lookup(X[t - 2])
            if q is not None:
                c = rup(X[t - 2] + (DHI - 1) * q[1] - 2 + EPS2)
                if c < best:
                    best, how, info = c, 2, q
        if t >= 3 and g3 is not None:
            q = g3.lookup(X[t - 3])
            if q is not None:
                c = rup(X[t - 3] + (DHI - 1) * q[1] - 3 + EPS3)
                if c < best:
                    best, how, info = c, 3, q
        X.append(best)
        if record:
            used.append((t, how, info))
    S = sum(X)
    out = dict(S=S, x0=X[0])
    if record:
        out['used'] = used
        out['X'] = X
    return out


ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))


def load_grids():
    """the repo's grid VALUES (data); used as upper bounds B_r(N)."""
    g2 = {}
    for k, v in json.load(open(os.path.join(ROOT, 'target1a', 'chain', 'grid_own.json'))).items():
        g2[int(k)] = v
    for k, v in json.load(open(os.path.join(ROOT, 'target7_threerise', 'b2_extra.json'))).items():
        g2[int(k)] = v
    for f in glob.glob(os.path.join(ROOT, 'target7b_push', 'b2_new*.json')):
        for k, v in json.load(open(f)).items():
            g2[int(k)] = v['B2'] if isinstance(v, dict) else v
    g3 = {}
    for f in glob.glob(os.path.join(ROOT, 'target7_threerise', 'grid3*.json')) + \
            glob.glob(os.path.join(ROOT, 'target7b_push', 'b3_new*.json')):
        for k, v in json.load(open(f)).items():
            g3[int(k)] = v['B3'] if isinstance(v, dict) else v
    return g2, g3
