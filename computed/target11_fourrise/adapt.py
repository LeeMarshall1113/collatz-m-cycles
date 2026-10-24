"""Adaptive exact B4 points.  The chain looks up B4 at the next grid point >= Y, which wastes up to a few percent of N
(= up to ~25 in B).  For the hardest shapes (hard.txt, least K) log every N = ceil(Y_{t-4}) the 4-step lookup asks for,
compute the missing exact B4(N) (b4join.exact; witness re-simulated), add them to b4_new_adapt.json, and iterate until
the hardest shapes' ratio stops changing.  The points are ordinary exact grid points valid for ALL shapes;
final acceptance is the full fastchain.py all-shapes run.
usage: python adapt.py m [--nshapes 12] [--maxN 600] [--batch 12]"""
import sys, os, json, math, time, bisect
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run11 as R            # noqa: E402
import b4join as J           # noqa: E402
CR = R.CR; C = CR.C; SC = CR.SC; F = R.fastshapes.F if hasattr(R.fastshapes, 'F') else None
from fractions import Fraction as F   # noqa: E402

AD = os.path.join(HERE, 'b4_new_adapt.json')


def hard_shapes(m, n):
    rows = sorted((int(K), int(p), int(e)) for K, p, e in
                  (l.split() for l in open(os.path.join(R.T10, 'hard.txt')) if not l.startswith('#')))
    return [(K, p) for K, p, e in rows if e <= m][:n]


def chain_log(m, K, p, g, d4keys):
    Ub = C.Ub_cert(m, K, p)[0]
    Y0 = CR.CHN.Y0_of(F(math.ceil(Ub)))
    Ys = [Y0]
    miss = set()
    G4 = g[4]
    while len(Ys) < m:
        t = len(Ys)
        best = CR.ceilF(C.DU * Ys[-1])
        for r in (2, 3, 4):
            if t < r:
                break
            B = g[r].B_for(Ys[t - r])
            if r == 4:
                N = math.ceil(F(Ys[t - 4], SC))
                if N not in d4keys:
                    miss.add(N)
            if B is None:
                continue
            b = Ys[t - r] + CR.ceilF((C.DU - 1) * B * SC) - r * SC + 1
            if b < best:
                best = b
        Ys.append(best)
    return sum(Ys) / (K * SC), miss


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d: (type(d)(a[a.index(k) + 1]) if k in a else d)
    m = int(a[0]); ns = opt('--nshapes', 12); maxN = opt('--maxN', 600); batch = opt('--batch', 12)
    shapes = hard_shapes(m, ns)
    d2, d3 = R.R7.load_b2(), R.R7.load_b3()
    while True:
        d4 = R.load_b4()
        g = {2: CR.Grid(list(d2.items())), 3: CR.Grid(list(d3.items())), 4: CR.Grid(list(d4.items()))}
        worst, miss = 0, set()
        for K, p in shapes:
            r, ms = chain_log(m, K, p, g, set(d4))
            worst = max(worst, r)
            miss |= {N for N in ms if 72 <= N <= maxN}
        print(f"m={m} grid pts {len(d4)} hard-shape worst ratio {worst:.5f}; missing queried N: {len(miss)} {sorted(miss)[:30]}", flush=True)
        if not miss or worst < 0.9:
            break
        todo = sorted(miss)[:batch]
        ad = json.load(open(AD)) if os.path.exists(AD) else {}
        for N in todo:
            t = time.time()
            b, w, tt = J.exact(N, verbose=False)
            assert J.runs_value(w) == b and 0 < w < 2 ** N and w % 2
            ad[str(N)] = dict(B4=b, witness=str(w), t=tt, secs=round(time.time() - t, 1))
            json.dump(ad, open(AD, 'w'), indent=0)
            print(f"  B4({N}) = {b} (N+{b - N}) {time.time() - t:.1f}s", flush=True)
