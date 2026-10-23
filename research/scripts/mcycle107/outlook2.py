"""Kernel-cost-minimal grid points for m (Lean mirror chain3.shape_ok3), B2 from grid103 plus the
research B2 grid (collatz-loop target7b), B3 from the research B3 grid.  Cost model (seconds):
B2 point N not in grid103: 3780 (N/60821)^2 (AllPairs 60821 took 63 min); B3 point N not built:
T3 * N^3 / 6 (T3 = kernel seconds per triple).  usage: python outlook2.py m [top2 top3]"""
import sys, os, time, json, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle105'))
import memguard; memguard.start(3.0e9)
a = sys.argv[1:]; sys.argv = [sys.argv[0]]
import threading
sys.setrecursionlimit(2000000); threading.stack_size(250 * 2 ** 20)
import chain3 as C
sys.setrecursionlimit(2000000)
T7B = "C:/Users/hackathon/Documents/GitHub/collatz-loop/research/target7b_push"
T7 = "C:/Users/hackathon/Documents/GitHub/collatz-loop/research/target7_threerise"
CH = "C:/Users/hackathon/Documents/GitHub/collatz-loop/research/target1a/chain"
T3 = float(os.environ.get("T3", "1e-3"))
m = int(a[0]); top2 = int(a[1]) if len(a) > 1 else 10**7; top3 = int(a[2]) if len(a) > 2 else 10**6
g103 = dict(C.grid103())


def load_b2():
    g = {}
    for f in glob.glob(os.path.join(CH, '**', 'grid_own.json'), recursive=True)[:1]:
        g.update({int(k): v for k, v in json.load(open(f)).items()})
    g.update({int(k): v for k, v in json.load(open(os.path.join(T7, 'b2_extra.json'))).items()})
    for f in glob.glob(os.path.join(T7B, 'b2_new*.json')):
        for k, v in json.load(open(f)).items():
            g[int(k)] = v['B2'] if isinstance(v, dict) else v
    return g


def load_b3():
    d = {}
    for f in glob.glob(os.path.join(T7, 'grid3*.json')) + glob.glob(os.path.join(T7B, 'b3_new*.json')):
        for k, v in json.load(open(f)).items():
            d[int(k)] = v['B3'] if isinstance(v, dict) else v
    return d


b2 = load_b2(); b2.update(g103); b3 = load_b3()
built3 = set(int(x) for x in os.environ.get('BUILT3', '79,122,203,325').split(','))


def c2(N): return 0 if N in g103 else 3780 * (N / 60821) ** 2   # AllPairs 60821: 63 min (LEDGER)
def c3(N): return 0 if N in built3 else T3 * N ** 3 / 6


def main():
    t = time.time()
    P = C.L.plan_m(m, need_ns=False)
    certs = P['certs']
    print(m, "nodes", P['nodes'], "shapes", len(certs), "%.0fs" % (time.time() - t), flush=True)
    hard = [None]

    def ok(S2, S3, used=None):
        g2 = sorted((N, b2[N]) for N in S2); g3 = sorted((N, b3[N]) for N in S3)
        if hard[0] is not None and not C.shape_ok3(m, g2, g3, hard[0])[0]:
            return False
        for c in certs:
            if not C.shape_ok3(m, g2, g3, c, used)[0]:
                hard[0] = c; return False
        return True
    S2 = {N for N in b2 if N <= top2} | set(g103); S3 = {N for N in b3 if N <= top3}
    if not ok(S2, S3):
        print(m, "FAILS with B2 <=", top2, "B3 <=", top3, flush=True); return
    used = set(); ok(S2, S3, used)
    S3 = {N for N, _ in used}
    # B2 points actually used: approximate by greedy removal below
    items = [(c3(N), 3, N) for N in S3 if c3(N) > 0] + [(c2(N), 2, N) for N in S2 if c2(N) > 0]
    for cst, kind, N in sorted(items, reverse=True):
        if kind == 3 and ok(S2, S3 - {N}): S3 = S3 - {N}
        elif kind == 2 and ok(S2 - {N}, S3): S2 = S2 - {N}
    n2 = sorted(N for N in S2 if c2(N) > 0); n3 = sorted(N for N in S3 if c3(N) > 0)
    print(m, "B3 used", sorted(S3), flush=True)
    print(m, "new B2", n2, "cost %.1f h" % (sum(map(c2, n2)) / 3600), flush=True)
    print(m, "new B3", n3, "cost %.1f h (T3=%g)" % (sum(map(c3, n3)) / 3600, T3), "%.0fs" % (time.time() - t), flush=True)


th = threading.Thread(target=main); th.start(); th.join()
