"""All Theorem-21-surviving shapes at m through the r-step chain (target10 chainr.py) with exact B2, B3, B4 grids.
usage: python run11.py m [m ...] [--b4top N] [--procs P] [--b4 none]
B2/B3 grids: as run7b.py (every value exact).  B4 grid: target10_rrise/b4_grid.json + b4_new_*.json here."""
import sys, os, json, glob, time, math
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
T7B = os.path.abspath(os.path.join(HERE, '..', 'target7b_push'))
T10 = os.path.abspath(os.path.join(HERE, '..', 'target10_rrise'))
for p in (T10, T7B, HERE):
    sys.path.insert(0, p)
import run7b as R7      # noqa: E402
import chainr as CR     # noqa: E402
import fastshapes       # noqa: E402


def load_b4(top=None):
    d = {}
    for f in [os.path.join(T10, 'b4_grid.json')] + sorted(glob.glob(os.path.join(HERE, 'b4_new_*.json'))):
        for k, v in json.load(open(f)).items():
            B = v['B4']
            assert B > int(k)
            d[int(k)] = B
    return {N: B for N, B in d.items() if top is None or N <= top}


G = None


def _init(d2, d3, d4):
    global G
    G = {2: CR.Grid(list(d2.items())), 3: CR.Grid(list(d3.items()))}
    if d4:
        G[4] = CR.Grid(list(d4.items()))


def _check(args):
    m, K, p = args
    r = CR.shape_check(m, K, p, G)
    return (K, p, r.get('why'), r.get('small', False), float(r.get('ratio', 0)), r.get('ok'),
            r.get('use'), r.get('maxN'))


def run(m, d2, d3, d4, procs=1):
    t = time.time()
    Kceil, surv = fastshapes.surviving(m)
    t1 = time.time()
    todo = [(m, K, p) for K, p in surv]
    if procs > 1:
        with Pool(procs, initializer=_init, initargs=(d2, d3, d4)) as pool:
            res = pool.map(_check, todo, chunksize=8)
    else:
        _init(d2, d3, d4)
        res = [_check(a) for a in todo]
    nfail = sum(1 for r in res if r[2] or not r[5])
    nsmall = sum(1 for r in res if r[3])
    rows = sorted([r for r in res if not r[2]], key=lambda r: -r[4])
    print(f"m={m} Kceil={Kceil:.4e} survivors={len(surv)} small(Ub<=X0)={nsmall} B2 top {max(d2)} ({len(d2)} pts) "
          f"B3 top {max(d3)} ({len(d3)} pts) B4 top {max(d4) if d4 else 0} ({len(d4) if d4 else 0} pts) "
          f"enum {t1 - t:.0f}s chain {time.time() - t1:.0f}s", flush=True)
    for r in rows[:5]:
        print(f"  ratio={r[4]:.5f} K={r[0]} ({r[0]:.4e}) use={r[6]} maxN={r[7]}", flush=True)
    print(f"  m={m}: worst ratio {rows[0][4]:.5f} at K={rows[0][0]}; failures {nfail}; "
          f"{'CLOSED' if nfail == 0 else 'NOT CLOSED'}", flush=True)
    if nfail:
        bad = [r for r in res if r[2] or not r[5]]
        print(f"  first failing shapes: {[(r[0], r[4]) for r in bad[:5]]}", flush=True)
    return nfail, rows


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d=None: (a[a.index(k) + 1] if k in a else d)
    procs = int(opt('--procs', 1))
    b4top = opt('--b4top')
    d2, d3 = R7.load_b2(), R7.load_b3()
    d4 = None if opt('--b4') == 'none' else load_b4(int(b4top) if b4top else None)
    ms, skip = [], False
    for x in a:
        if skip:
            skip = False
            continue
        if x.startswith('--'):
            skip = True
            continue
        ms.append(int(x))
    for m in ms:
        run(m, d2, d3, d4, procs)
