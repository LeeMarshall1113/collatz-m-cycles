"""Referee (target 7b): own implementation of the 1/2/3-step chain, exact rationals, no rounding.

Bounds (all upper bounds on x_t = log2(n_t + 1), n_t > 2^71 the local minima from the least):
  x_0 <= log2(ceil(Ub))                                  Ub from Theorem 21 at floor X = n_0
  x_t <= DLT * x_{t-1}                                   Lemma 20 (DLT >= log2 3)
  x_t <= x_{t-2} + (DLT-1) B2(N) - 2 + 6/2^71            Alick two-step, N >= x_{t-2}
  x_t <= x_{t-3} + (DLT-1) B3(N) - 3 + 4/2^71            Lemma 3S, N >= x_{t-3}
Excluded iff sum_{t<m} Y_t < K (Lemma 8).
DLT: either the paper's DU = 1.58496250072116 (as in the Theorem-21 G(j)) or a tight rational upper
bound of log2 3; both are reported.
usage: python mychain.py hard            # the two hard shapes at m=121 (and 110, 116)
       python mychain.py usage FILE.pkl  # all survivors in FILE (list of (K,p)), m from file
"""
import sys, os, json, glob, math, pickle, time
from fractions import Fraction as F
from mpmath import mp, mpf, log as mlog, iv

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.abspath(os.path.join(HERE, '..'))

mp.dps = 80
iv.dps = 80
# rigorous enclosure of log2 3 and ln 2
_l3 = iv.log(3) / iv.log(2)
_ln2 = iv.log(2)
from mpmath.libmp import to_rational
D_LO = F(*map(int, to_rational(_l3._mpi_[0])))
D_HI = F(*map(int, to_rational(_l3._mpi_[1])))
LN2_LO = F(*map(int, to_rational(_ln2._mpi_[0])))
assert D_HI - D_LO < F(1, 10 ** 70)
DU = F(158496250072116, 10 ** 14)
assert DU > D_HI
X0 = 2 ** 71 + 1
E2 = F(6, 2 ** 71)
E3 = F(4, 2 ** 71)


def Gsum(j):
    s, t = F(0), F(1)
    for _ in range(j):
        s += t
        t *= DU
    return s


_GC = {}


def G(j):
    if j not in _GC:
        _GC[j] = Gsum(j)
    return _GC[j]


def theorem21_Ub(m, K, p, cap=400, with_m2zero=True):
    """least Ub over admissible (m2, N, M) with n_0 < Ub.  Lambda > (p - K D_HI) LN2_LO =: lo.
    Theorem 21: Lambda < (m - m2)/n0 + 1/(2^N - 1) + (m2-1)/(2^M - 1) with N m G(m2) <= m2 K,
    M m (1 + G(m2-1)) <= m2 K.  Remark 7 (m2 = 0): Lambda < m / n0."""
    lo = (p - K * D_HI) * LN2_LO
    assert lo > 0
    best = None
    if with_m2zero:
        best = (F(m) / lo, 0)
    for m2 in range(1, m + 1):
        N = (m2 * K * G(m2).denominator) // (m * G(m2).numerator)
        g1 = 1 + G(m2 - 1)
        M = (m2 * K * g1.denominator) // (m * g1.numerator)
        N, M = min(N, cap), min(M, cap)
        if N < 1 or M < 1:
            continue
        # verify admissibility exactly
        assert N * m * G(m2) <= m2 * K and M * m * g1 <= m2 * K
        room = lo - F(1, 2 ** N - 1) - F(m2 - 1, 2 ** M - 1)
        if room <= 0:
            continue
        Ub = F(m - m2) / room
        if best is None or Ub < best[0]:
            best = (Ub, m2, N, M)
    return best


def log2_up(c):
    """rational upper bound for log2(c), c a positive integer"""
    v = iv.log(iv.mpf(c)) / iv.log(2)
    return F(*map(int, to_rational(v._mpi_[1]))) + F(1, 10 ** 60)


def load_grids():
    b2 = {}
    for k, v in json.load(open(os.path.join(R, 'target1a', 'chain', 'grid_own.json'))).items():
        b2[int(k)] = int(v)
    for k, v in json.load(open(os.path.join(R, 'target7_threerise', 'b2_extra.json'))).items():
        b2[int(k)] = int(v)
    for f in sorted(glob.glob(os.path.join(R, 'target7b_push', 'b2_new_g*.json'))):
        for k, v in json.load(open(f)).items():
            b2[int(k)] = int(v['B2'])
    b3 = {}
    for f in sorted(glob.glob(os.path.join(R, 'target7_threerise', 'grid3_p*.json'))) + \
            sorted(glob.glob(os.path.join(R, 'target7b_push', 'b3_new_g*.json'))):
        for k, v in json.load(open(f)).items():
            b3[int(k)] = int(v['B3'])
    return b2, b3


class MinGrid:
    """min over grid points N >= y of B(N) (no monotonicity assumed); returns (B, N_argmin)"""
    def __init__(self, d):
        self.Ns = sorted(d)
        self.suf = [None] * len(self.Ns)
        best = None
        for i in range(len(self.Ns) - 1, -1, -1):
            N = self.Ns[i]
            if best is None or d[N] < best[0]:
                best = (d[N], N)
            self.suf[i] = best

    def get(self, y):
        import bisect
        c = math.ceil(y)
        i = bisect.bisect_left(self.Ns, c)
        return None if i == len(self.Ns) else self.suf[i]


def chain(m, Y0, g2, g3, dlt):
    Ys = [Y0]
    used2, used3 = set(), set()
    use = [0, 0, 0, 0]
    for t in range(1, m):
        best, how, which = dlt * Ys[t - 1], 1, None
        if g2 is not None and t >= 2:
            r = g2.get(Ys[t - 2])
            if r is not None:
                b = Ys[t - 2] + (dlt - 1) * r[0] - 2 + E2
                if b < best:
                    best, how, which = b, 2, r[1]
        if g3 is not None and t >= 3:
            r = g3.get(Ys[t - 3])
            if r is not None:
                b = Ys[t - 3] + (dlt - 1) * r[0] - 3 + E3
                if b < best:
                    best, how, which = b, 3, r[1]
        use[how] += 1
        if how == 2:
            used2.add(which)
        elif how == 3:
            used3.add(which)
        # keep denominators bounded: round UP to a dyadic with 200 fractional bits
        num = best.numerator << 200
        q = -((-num) // best.denominator)
        Ys.append(F(q, 1 << 200))
    return Ys, use, used2, used3


def check_shape(m, K, p, g2, g3, dlt=DU, with_m2zero=False):
    r = theorem21_Ub(m, K, p, with_m2zero=with_m2zero)
    if r is None:
        return dict(ok=False, why='no room')
    Ub = r[0]
    if Ub <= X0:
        return dict(ok=True, small=True, ratio=F(0), m2=r[1])
    c = math.ceil(Ub)            # n0 < Ub  =>  n0 + 1 <= ceil(Ub)
    Y0 = log2_up(c)
    Ys, use, u2, u3 = chain(m, Y0, g2, g3, dlt)
    S = sum(Ys)
    return dict(ok=S < K, ratio=S / K, m2=r[1], Y0=Y0, use=use, u2=u2, u3=u3, Ys=Ys)


def pfor(K):
    """least p with p > K log2 3 (the only candidate p in the thin strip)"""
    p = (K * D_LO.numerator) // D_LO.denominator + 1
    assert p > K * D_HI and p - 1 < K * D_LO
    return p


if __name__ == "__main__":
    b2, b3 = load_grids()
    print("grids: B2", len(b2), "pts top", max(b2), " B3", len(b3), "pts top", max(b3), flush=True)
    g2, g3 = MinGrid(b2), MinGrid(b3)
    if sys.argv[1] == 'hard':
        for m in (110, 116, 121, 122):
            for K in (77692117359936589403, 27444133206411171953):
                p = pfor(K)
                for dlt, nm in ((DU, 'DU'), (D_HI, 'log2_3_hi')):
                    for z in (False, True):
                        r = check_shape(m, K, p, g2, g3, dlt, with_m2zero=z)
                        print(f"m={m} K={K} p={p} dlt={nm} m2zero={z} ratio={float(r['ratio']):.6f} "
                              f"ok={r['ok']} m2={r['m2']} log2(n0+1)<={float(r['Y0']):.4f} use={r['use'][1:]} "
                              f"maxB2N={max(r['u2']) if r['u2'] else 0} maxB3N={max(r['u3']) if r['u3'] else 0}",
                              flush=True)
                r = check_shape(m, K, p, g2, g3)
                print("   B2 used:", sorted(r['u2']))
                print("   B3 used:", sorted(r['u3']))
                print("   Ys:", [round(float(y), 3) for y in r['Ys']], flush=True)
    elif sys.argv[1] == 'usage':
        d = pickle.load(open(sys.argv[2], 'rb'))
        m, surv = d['m'], d['surv']
        drop2 = set(json.loads(sys.argv[3])) if len(sys.argv) > 3 else set()
        drop3 = set(json.loads(sys.argv[4])) if len(sys.argv) > 4 else set()
        if drop2 or drop3:
            g2 = MinGrid({N: B for N, B in b2.items() if N not in drop2})
            g3 = MinGrid({N: B for N, B in b3.items() if N not in drop3})
        t0 = time.time()
        U2, U3 = set(), set()
        worst = (F(0), None)
        nfail = 0
        for i, (K, p) in enumerate(surv):
            r = check_shape(m, K, p, g2, g3)
            if not r['ok']:
                nfail += 1
                print("FAIL", K, p, r.get('why'), float(r.get('ratio', 0)), flush=True)
            if r.get('small'):
                continue
            U2 |= r['u2']
            U3 |= r['u3']
            if r['ratio'] > worst[0]:
                worst = (r['ratio'], K)
        print(f"m={m} shapes={len(surv)} failures={nfail} worst={float(worst[0]):.6f} at K={worst[1]} "
              f"({time.time() - t0:.0f}s)")
        print("B2 used", len(U2), json.dumps(sorted(U2)))
        print("B3 used", len(U3), json.dumps(sorted(U3)), flush=True)
