"""[heuristic] What does m = 128, 129, ... need?  Real B2/B3/B4 grids plus SYNTHETIC points from the gap model
    B_r(N) = N + ceil((r-1) log2 N - log2((r-1)!) + b)
(fit: target10 calib, b ~ -0.7 mean, +6 pessimistic).  Synthetic points either 'dense' (every integer N, i.e. a
perfectly adaptive grid) or 5% apart.  Only the hard shape K = 27444133206411171953 (worst for m in 110..144).
usage: python explore.py   (prints a scenario table)"""
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import trace as T    # noqa: E402


def gap(r, N, b):
    return math.ceil((r - 1) * math.log2(N) - math.log2(math.factorial(r - 1)) + b)


def add_synth(d, r, lo, hi, b, dense=True):
    real = dict(d)
    rk = sorted(real)
    d = dict(d)
    N = lo
    import bisect
    while N <= hi:
        if N not in d:
            v = N + gap(r, N, b)
            i = bisect.bisect_right(rk, N) - 1        # B_r is non-decreasing in N: never below a real point under N
            if i >= 0:
                v = max(v, real[rk[i]])
            d[N] = v
        N = N + 1 if dense else int(N * 1.05) + 1
    return d


BASE = T.base_grids()


def scen(b5=0, b6=0, t4=None, t3=None, t2=None, b=0.0, dense=True, dense4=False):
    g = {r: dict(v) for r, v in BASE.items()}
    if dense4:
        g[4] = add_synth(g[4], 4, 72, 852, b, True)   # fill gaps of the real B4 grid (lookup waste)
    if t4:
        g[4] = add_synth(g[4], 4, 853, t4, b, dense)
    if t3:
        g[3] = add_synth(g[3], 3, 38244, t3, b, dense)
    if t2:
        g[2] = add_synth(g[2], 2, 1039711, t2, b, dense)
    if b5:
        g[5] = add_synth({}, 5, 72, b5, b, dense)
    if b6:
        g[6] = add_synth({}, 6, 72, b6, b, dense)
    return T.mk(g)


def last_m(G, lo=127, hi=160):
    m = lo
    while m < hi and float(T.run(m + 1, T.HARD, G)[0]) < 1:
        m += 1
    r, Ys, how, Ns = T.run(m, T.HARD, G)
    used = {}
    for h, N in zip(how, Ns):
        if N:
            used[h] = max(used.get(h, 0), N[0])
    return m, float(r), float(T.run(m + 1, T.HARD, G)[0]), used


if __name__ == "__main__":
    rows = [("real grids", {}),
            ("B4 gaps filled (dense <=852)", dict(dense4=True)),
            ("B5 to 80", dict(b5=80)), ("B5 to 100", dict(b5=100)), ("B5 to 120", dict(b5=120)),
            ("B5 to 150", dict(b5=150)), ("B5 to 200", dict(b5=200)), ("B5 to 300", dict(b5=300)),
            ("B5 to 120, b=+6", dict(b5=120, b=6)), ("B5 to 150, b=+6", dict(b5=150, b=6)),
            ("B5 to 200, b=+6", dict(b5=200, b=6)),
            ("B5 to 150, 5% spacing", dict(b5=150, dense=False)),
            ("B5 to 200, 5% spacing", dict(b5=200, dense=False)),
            ("B4 to 1000", dict(t4=1000)), ("B4 to 1200", dict(t4=1200)), ("B4 to 1400", dict(t4=1400)),
            ("B4 to 1600", dict(t4=1600)),
            ("B3 to 50k", dict(t3=50000)), ("B3 to 60k", dict(t3=60000)), ("B3 to 70k", dict(t3=70000)),
            ("B3 to 90k", dict(t3=90000)), ("B3 to 60k, 5%", dict(t3=60000, dense=False)),
            ("B2 to 1.6e6", dict(t2=1600000)), ("B2 to 2.6e6", dict(t2=2600000)), ("B2 to 4e6", dict(t2=4000000)),
            ("B5 200 + B6 120", dict(b5=200, b6=120)),
            ("B5 300 + B4 1400 + B3 90k", dict(b5=300, t4=1400, t3=90000)),
            ]
    for name, kw in rows:
        m, r, r1, used = last_m(scen(**kw))
        print(f"{name:32s} last m={m} ratio {r:.4f} (m+1: {r1:.3f}) max lookup N per r {used}", flush=True)
