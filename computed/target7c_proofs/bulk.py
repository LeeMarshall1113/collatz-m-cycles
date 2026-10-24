"""Exact bulk check of every shape in a survivor file (independent code, indep.py).

For each shape: (1) independent Theorem-21 survival filter (indep.survives) -- shapes it rejects are
excluded outright; (2) a rigorous Ub from ONE admissible m2 (chosen by a float heuristic; any
admissible m2 gives a valid bound, the bound itself is exact); if that m2 has no room, all m2 are
tried; (3) x0u = j/64 with U^64 <= 2^j (U = ceil(Ub) >= n0 + 1), exact integer test;
(4) S(x0u) from a table of exact chains at x0 = j/64, valid because S is nondecreasing in x0;
(5) S < K.  Any shape failing the screen is re-done with the full indep.chain.
usage: python bulk.py m survfile [procs]"""
import sys, math, time
from fractions import Fraction as F
from multiprocessing import Pool
import indep as I

G2 = G3 = None
TAB = {}
M = None


def _init(m):
    global G2, G3, M
    a, b = I.load_grids()
    G2, G3 = I.Grid(a), I.Grid(b)
    M = m


def S_at(j):
    if j not in TAB:
        TAB[j] = I.chain_x0(M, F(j, 64), G2, G3)['S']
    return TAB[j]


def ub_one(m, K, p, m2):
    lam_lo = p * I.LN2LO - K * I.LN3HI
    N = min(I.NCAP, math.floor(F(m2 * K) / (m * I.G(m2))))
    Mm = min(I.NCAP, math.floor(F(m2 * K) / (m * (1 + I.G(m2 - 1)))))
    if N < 1 or Mm < 1:
        return None
    room = lam_lo - F(1, 2 ** N - 1) - F(m2 - 1, 2 ** Mm - 1)
    if room <= 0:
        return None
    if m2 == m:
        return 'contra'
    return F(m - m2) / room


def best_m2_float(m, K, p):
    lam = float(p - K * I.DHI) * 0.6931471805599453
    best = None
    G = 1.0
    gs = [0.0]
    d = 1.5849625007211562
    for j in range(1, m + 1):
        gs.append(gs[-1] + d ** (j - 1))
    for m2 in range(1, m + 1):
        N = min(600, math.floor(m2 * K / (m * gs[m2])))
        Mm = min(600, math.floor(m2 * K / (m * (1 + gs[m2 - 1]))))
        if N < 1 or Mm < 1:
            continue
        room = lam - 1 / (2.0 ** N - 1) - (m2 - 1) / (2.0 ** Mm - 1)
        if room <= 0:
            continue
        u = (m - m2) / room if m2 < m else 0
        if best is None or u < best[0]:
            best = (u, m2)
    return best[1] if best else None


def one(args):
    m, K, p = args
    if not I.survives(m, K, p):
        return (K, p, 'rejected-by-indep-filter', 0.0, True)
    m2 = best_m2_float(m, K, p)
    Ub = ub_one(m, K, p, m2) if m2 else None
    if Ub is None:
        r = I.thm21_Ub(m, K, p)
        if r is None:
            return (K, p, 'NO ROOM', 9.9, False)
        Ub = 'contra' if r[0] == 'contra' else r[0]
    if Ub == 'contra':
        return (K, p, 'contra', 0.0, True)
    if Ub <= I.X0:
        return (K, p, 'Ub<=X0', 0.0, True)
    U = math.ceil(Ub)
    j = (U.bit_length() - 1) * 64
    U64 = U ** 64
    while U64 > (1 << j):
        j += 1
    S = S_at(j)
    if S < K:
        return (K, p, 'screen', float(S / K), True)
    r = I.chain(m, K, p, G2, G3)
    return (K, p, 'full', float(r['ratio']), bool(r['ok']))


if __name__ == "__main__":
    m = int(sys.argv[1])
    rows = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if not l.startswith('#')]
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    t = time.time()
    todo = [(m, K, p) for K, p in rows]
    if procs > 1:
        with Pool(procs, initializer=_init, initargs=(m,)) as pool:
            res = pool.map(one, todo, chunksize=256)
    else:
        _init(m)
        res = [one(x) for x in todo]
    from collections import Counter
    fails = [r for r in res if not r[4]]
    res.sort(key=lambda r: -r[3])
    print(f"m={m} shapes {len(res)} kinds {dict(Counter(r[2] for r in res))} FAILURES {len(fails)} "
          f"time {time.time() - t:.0f}s", flush=True)
    for r in res[:6]:
        print(f"  ratio<={r[3]:.6f} K={r[0]} p={r[1]} via {r[2]}", flush=True)
    for r in fails[:20]:
        print("  FAIL", r, flush=True)
