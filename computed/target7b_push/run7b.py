"""All Theorem-21-surviving shapes at m (fast exact enumeration, fastshapes.py) through the
three-step chain (target7_threerise/chain3.py) with B2 + B3 grids.
usage: python run7b.py m [m ...] [--b3top N] [--b2top N] [--procs P] [--b3 none]
B2 grid: target1a/chain/grid_own.json + target7_threerise/b2_extra.json + b2_new.json (here)
B3 grid: target7_threerise/grid3_p*.json + b3_new*.json (here); every value exact.
"""
import sys, os, json, glob, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
T7 = os.path.abspath(os.path.join(HERE, '..', 'target7_threerise'))
sys.path.insert(0, T7)
sys.path.insert(0, HERE)
import chain3 as C3     # noqa: E402
import fastshapes       # noqa: E402


def load_b2(top=None):
    g = {int(k): v for k, v in json.load(open(os.path.join(C3.CH, 'grid_own.json'))).items()}
    g.update({int(k): v for k, v in json.load(open(os.path.join(T7, 'b2_extra.json'))).items()})
    for f in glob.glob(os.path.join(HERE, 'b2_new*.json')):
        for k, v in json.load(open(f)).items():
            g[int(k)] = v['B2'] if isinstance(v, dict) else v
    return {N: B for N, B in g.items() if top is None or N <= top}


def load_b3(top=None):
    d = {}
    for f in glob.glob(os.path.join(T7, 'grid3*.json')) + glob.glob(os.path.join(HERE, 'b3_new*.json')):
        for k, v in json.load(open(f)).items():
            B = v['B3'] if isinstance(v, dict) else v
            assert B is not None and B >= int(k)
            d[int(k)] = B
    return {N: B for N, B in d.items() if top is None or N <= top}


G2 = G3 = None


def _init(d2, d3):
    global G2, G3
    G2 = C3.Grid(list(d2.items()))
    G3 = C3.Grid(list(d3.items())) if d3 else None


def _check(args):
    m, K, p = args
    r = C3.shape_check3(m, K, p, G2, G3)
    return (K, p, r.get('why'), r.get('small', False), float(r.get('ratio', 0)), r.get('ok'),
            r.get('use'), r.get('maxN'))


def run(m, d2, d3, procs=1):
    t = time.time()
    Kceil, surv = fastshapes.surviving(m)
    t1 = time.time()
    todo = [(m, K, p) for K, p in surv]
    if procs > 1:
        with Pool(procs, initializer=_init, initargs=(d2, d3)) as pool:
            res = pool.map(_check, todo, chunksize=8)
    else:
        _init(d2, d3)
        res = [_check(a) for a in todo]
    nfail = sum(1 for r in res if r[2] or not r[5])
    nsmall = sum(1 for r in res if r[3])
    rows = sorted([r for r in res if not r[2]], key=lambda r: -r[4])
    print(f"m={m} Kceil={Kceil:.4e} survivors={len(surv)} small(Ub<=X0)={nsmall} "
          f"B2 top {max(d2)} ({len(d2)} pts)  B3 top {max(d3) if d3 else 0} ({len(d3) if d3 else 0} pts)  "
          f"enum {t1 - t:.0f}s chain {time.time() - t1:.0f}s", flush=True)
    for r in rows[:5]:
        print(f"  ratio={r[4]:.5f} K={r[0]} ({r[0]:.4e}) use={r[6]} maxN={r[7]}", flush=True)
    print(f"  m={m}: worst ratio {rows[0][4]:.5f} at K={rows[0][0]}; failures {nfail}; "
          f"{'CLOSED' if nfail == 0 else 'NOT CLOSED'}", flush=True)
    return nfail, rows


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d=None: (a[a.index(k) + 1] if k in a else d)
    b3top = opt('--b3top'); b2top = opt('--b2top')
    procs = int(opt('--procs', 1))
    d2 = load_b2(int(b2top) if b2top else None)
    d3 = None if opt('--b3') == 'none' else load_b3(int(b3top) if b3top else None)
    ms = []
    skip = False
    for x in a:
        if skip:
            skip = False
            continue
        if x.startswith('--'):
            skip = x != '--all'
            continue
        ms.append(int(x))
    for m in ms:
        run(m, d2, d3, procs)
