"""All-shapes chain for m >= 128: target11_fourrise/fastchain.py, same mathematics, with
  * shapes13.patch(): fastshapes.box_points with the endpoint y-window (referee F1),
  * extra exact grid points from target13_m128/b2_new_*.json, b3_new_*.json (keys N -> {"B2"/"B3": value, ...}),
  * ONE process (no Pool), and candidates streamed interval by interval (bounded memory),
  * a global top-`top` list of screen bounds re-run exactly, as in fastchain.
usage: python fastchain13.py m [m ...] [--top 300] [--tries 4] [--b4top 852]"""
import sys, os, json, glob, time, heapq, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import shapes13           # noqa: E402
shapes13.patch()
sys.path.insert(0, os.path.join(HERE, '..', 'target11_fourrise'))
import fastchain as FC    # noqa: E402
from fractions import Fraction as F   # noqa: E402
R, fs, C = FC.R, FC.fs, FC.C
assert fs.box_points is shapes13.box_points


def extra(kind):
    d = {}
    for f in sorted(glob.glob(os.path.join(HERE, f'b{kind}_new_*.json'))):
        for k, v in json.load(open(f)).items():
            B = v[f'B{kind}']
            assert B > int(k)
            d[int(k)] = B
    return d


def run(m, d2, d3, d4, top):
    t0 = time.time()
    FC._init(d2, d3, d4)
    Kceil = fs.shapes.rhin_ceiling(m)
    iv = fs.merge(fs.intervals(m, Kceil))
    n = nscreen = 0
    need, heap = [], []
    seen_last = set()
    for Ka, Kb, L in iv:
        eta = F(L) / C.L2LO * (1 + F(1, 10 ** 9))
        pts = sorted(set(p for p in fs.box_points(Ka, Kb, eta)[0] if 1 <= p[0] < Kceil))
        n += len(pts)
        for K, p in pts:
            b = FC.cheap_Y0(m, K, p, FC.TRIES)
            if b is None:
                need.append((K, p)); continue
            if b == 0:
                continue
            S = FC.bucket_sum(m, b)
            if S >= K * FC.SC:
                need.append((K, p)); continue
            nscreen += 1
            item = (S / (K * FC.SC), K, p)
            if len(heap) < top:
                heapq.heappush(heap, item)
            elif item > heap[0]:
                heapq.heapreplace(heap, item)
    t1 = time.time()
    ranked = sorted(heap, reverse=True)
    nfail, worst = 0, None
    for K, p in need + [(K, p) for _, K, p in ranked]:
        r = FC.exact((m, K, p))
        if r[2] is None and len(r) == 3:
            continue
        K, p, why, small, ratio, ok, use, maxN = r
        if why or not ok:
            nfail += 1
            print(f"  FAIL K={K} p={p} why={why} ratio={ratio}", flush=True)
        if not why and (worst is None or ratio > worst[0]):
            worst = (ratio, K, use, maxN)
    cut = ranked[-1][0] if len(ranked) >= top else 0.0
    print(f"m={m} Kceil={Kceil:.4e} candidates={n} screened-closed={nscreen} exact-needed={len(need)} failures={nfail} "
          f"B2top={max(d2)} B3top={max(d3)} B4top={max(d4)} enum+screen {t1 - t0:.0f}s exact {time.time() - t1:.0f}s", flush=True)
    if worst:
        print(f"  m={m}: worst exact ratio {worst[0]:.6f} at K={worst[1]} use={worst[2]} maxN={worst[3]} "
              f"(worst valid as global max: {worst[0] >= cut}; cut bound {cut:.6f}); failures {nfail}; "
              f"{'CLOSED' if nfail == 0 else 'NOT CLOSED'}", flush=True)
    return nfail, worst


if __name__ == "__main__":
    a = sys.argv[1:]
    opt = lambda k, d=None: (a[a.index(k) + 1] if k in a else d)
    top = int(opt('--top', 300)); FC.TRIES = int(opt('--tries', 4))
    d2, d3 = R.R7.load_b2(), R.R7.load_b3()
    d2.update(extra(2)); d3.update(extra(3))
    d4 = R.load_b4(int(opt('--b4top', 852)))
    ms, skip = [], False
    for x in a:
        if skip:
            skip = False; continue
        if x.startswith('--'):
            skip = True; continue
        ms.append(int(x))
    for m in ms:
        run(m, d2, d3, d4, top)
