"""All-shapes r-step chain, fast screened version of run11.py (same mathematics, same grids).

For each m: candidates = fastshapes' lattice points (a superset of the Theorem-21 survivors; the
exact common.survives filter is applied only where needed).  For a candidate (K, p):
  * Ub' = (m - m2) / (lo - tail(m2, N, M)) for the few LARGEST m2 with room > 0, minimum taken.
    Any single m2 gives a valid upper bound, so Ub' >= Ub_cert's Ub (the minimum over all m2).
  * chain sum S(Y0b), Y0b = log2(Ub') rounded UP to a multiple of 2^-8 (+1e-6 safety) in 2^-64 units.
    The chain is monotone in Y0 (min of increasing maps), so  ratio <= S(Y0b) / (K 2^S).
  * ratio bound < 1 => the candidate is closed whether or not it survives Theorem 21.
Otherwise (bound >= 1, or any irregularity) it falls back to the literal run11 test: common.survives
(skip if refuted) and chainr.shape_check (exact rationals, interval logs).
The reported worst ratio / shape is EXACT: the TOP shapes by bound are re-run through shape_check and the
worst exact ratio is only accepted if it is >= the bound of every shape not re-run.
usage: python fastchain.py m [m ...] [--procs P] [--b4top N] [--b4 none] [--top 300] [--tries 4]"""
import sys, os, math, time
from fractions import Fraction as F
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import run11 as R       # noqa: E402
CR, fs = R.CR, R.fastshapes
C = CR.C
SC = CR.SC
BUCK = 256
G = None
CACHE = {}
TRIES = 4


def candidates(m):
    Kceil = fs.shapes.rhin_ceiling(m)
    iv = fs.merge(fs.intervals(m, Kceil))
    cand = []
    for Ka, Kb, L in iv:
        eta = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
        cand.extend(fs.box_points(Ka, Kb, eta)[0])
    return Kceil, sorted(set(p for p in cand if 1 <= p[0] < Kceil))


def _init(d2, d3, d4):
    global G
    R._init(d2, d3, d4)
    G = R.G


def cheap_Y0(m, K, p, tries):
    lo = (p - K * C.DHI) * C.L2LO
    if lo <= 0:
        return None
    best, n = None, 0
    for m2 in range(m - 1, 0, -1):
        r = C.NM(m, m2, K)
        if r is None:
            continue
        room = lo - C.tail(m2, *r)
        if room <= 0:
            continue
        Ub = F(m - m2) / room
        if best is None or Ub < best:
            best = Ub
        n += 1
        if n >= tries:
            break
    if best is None:
        return None
    if best <= C.X0:
        return 0
    l2 = math.log2(float(best)) + 1e-6
    b = math.ceil(l2 * BUCK)
    return b


def bucket_sum(m, b):
    key = (m, b)
    s = CACHE.get(key)
    if s is None:
        Y0 = (b * SC) // BUCK + 1
        Ys, _, _ = CR.chainr(m, Y0, G)
        s = sum(Ys)
        CACHE[key] = s
    return s


def screen(args):
    m, chunk, top = args
    ranked, need, nnone = [], [], 0
    for K, p in chunk:
        b = cheap_Y0(m, K, p, TRIES)
        if b is None:
            need.append((K, p)); continue
        if b == 0:
            continue
        S = bucket_sum(m, b)
        if S >= K * SC:
            need.append((K, p)); continue
        ranked.append((S / (K * SC), K, p))
    ranked.sort(reverse=True)
    return ranked[:top], need, len(ranked)


def exact(args):
    m, K, p = args
    if not C.survives(m, K, p):
        return (K, p, None)
    return (K, p) + tuple(R._check((m, K, p))[2:])


def run(m, d2, d3, d4, procs, top):
    t0 = time.time()
    Kceil, cand = candidates(m)
    t1 = time.time()
    n = len(cand)
    cs = max(1, n // (procs * 40))
    chunks = [(m, cand[i:i + cs], top) for i in range(0, n, cs)]
    with Pool(procs, initializer=_init, initargs=(d2, d3, d4)) as pool:
        res = pool.map(screen, chunks, chunksize=1)
        ranked = sorted((x for r in res for x in r[0]), reverse=True)
        need = [x for r in res for x in r[1]]
        nscreen = sum(r[2] for r in res)
        t2 = time.time()
        # exact re-run: shapes needing it + top-ranked shapes
        todo = [(m, K, p) for K, p in need] + [(m, K, p) for _, K, p in ranked[:top]]
        ex = pool.map(exact, todo, chunksize=4)
    nfail = 0
    worst = None
    for r in ex:
        if r[2] is None and len(r) == 3:
            continue           # refuted by Theorem 21 (not a survivor)
        K, p, why, small, ratio, ok, use, maxN = r
        if why or not ok:
            nfail += 1
        if not why and (worst is None or ratio > worst[0]):
            worst = (ratio, K, use, maxN)
    # acceptance of the worst: every shape not re-run has bound <= the (top+1)-th bound
    floor = ranked[top][0] if len(ranked) > top else 0.0   # ranked holds <= top per chunk; conservative below
    allb = sorted((x[0] for x in ranked), reverse=True)
    topb_cut = allb[top - 1] if len(allb) >= top else 0.0
    worst_ok = worst is not None and worst[0] >= topb_cut
    print(f"m={m} Kceil={Kceil:.4e} candidates={n} screened-closed={nscreen} exact-needed={len(need)} "
          f"failures={nfail} B4top={max(d4) if d4 else 0} enum {t1 - t0:.0f}s screen {t2 - t1:.0f}s exact {time.time() - t2:.0f}s",
          flush=True)
    if worst:
        print(f"  m={m}: worst exact ratio {worst[0]:.6f} at K={worst[1]} use={worst[2]} maxN={worst[3]} "
              f"(worst valid as global max: {worst_ok}; cut bound {topb_cut:.6f}); failures {nfail}; "
              f"{'CLOSED' if nfail == 0 else 'NOT CLOSED'}", flush=True)
    return nfail, worst


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d=None: (a[a.index(k) + 1] if k in a else d)
    procs = int(opt('--procs', 3)); top = int(opt('--top', 300)); TRIES = int(opt('--tries', 4))
    b4top = opt('--b4top')
    d2, d3 = R.R7.load_b2(), R.R7.load_b3()
    d4 = None if opt('--b4') == 'none' else R.load_b4(int(b4top) if b4top else None)
    ms, skip = [], False
    for x in a:
        if skip:
            skip = False; continue
        if x.startswith('--'):
            skip = True; continue
        ms.append(int(x))
    for m in ms:
        run(m, d2, d3, d4, procs, top)
