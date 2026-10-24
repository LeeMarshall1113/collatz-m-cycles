"""Run the independent chain (indep.py) over every shape in a survivor file; report worst ratios.
usage: python chain_all.py m survfile [procs] [--sample n]"""
import sys, time, random
from multiprocessing import Pool
import indep as I

G2 = G3 = None


def _init():
    global G2, G3
    a, b = I.load_grids()
    G2, G3 = I.Grid(a), I.Grid(b)


def _one(args):
    m, K, p = args
    if not I.survives(m, K, p):
        return (K, p, 'not-surviving(indep)', 0.0, True)
    r = I.chain(m, K, p, G2, G3)
    return (K, p, r.get('why', ''), float(r['ratio']) if 'ratio' in r else -1, bool(r['ok']), r['ratio'] if 'ratio' in r else None)


if __name__ == "__main__":
    a = sys.argv[1:]
    m = int(a[0])
    rows = [tuple(map(int, l.split())) for l in open(a[1]) if not l.startswith('#')]
    procs = int(a[2]) if len(a) > 2 and not a[2].startswith('--') else 1
    if '--sample' in a:
        random.seed(7)
        rows = random.sample(rows, int(a[a.index('--sample') + 1]))
    t = time.time()
    todo = [(m, K, p) for K, p in rows]
    if procs > 1:
        with Pool(procs, initializer=_init) as pool:
            res = pool.map(_one, todo, chunksize=64)
    else:
        _init()
        res = [_one(x) for x in todo]
    fails = [r for r in res if not r[4]]
    nots = [r for r in res if r[2].startswith('not-surv')]
    res.sort(key=lambda r: -r[3])
    print(f"m={m} shapes {len(res)} failures {len(fails)} not-surviving-by-indep-filter {len(nots)} "
          f"time {time.time() - t:.0f}s", flush=True)
    for r in res[:6]:
        print(f"  ratio={r[3]:.6f} K={r[0]} p={r[1]} {r[2]}")
    if res and res[0][5] is not None:
        print("  worst ratio exact < 1:", res[0][5] < 1)
