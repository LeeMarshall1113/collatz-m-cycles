"""exact B4 grid points (b4join.exact), each witness re-simulated; appends to b4_grid.json.
usage: python grid4.py N1 N2 ... | --geom START STOP RATIO"""
import sys, os, json, time
import b4join as J
a = sys.argv[1:]
if a[0] == '--geom':
    N, stop, ratio = int(a[1]), int(a[2]), float(a[3])
    Ns = []
    while N <= stop:
        Ns.append(N); N = int(N * ratio) + 1
else:
    Ns = list(map(int, a))
f = os.environ.get('GRID', 'b4_grid.json')
d = json.load(open(f)) if os.path.exists(f) else {}
for N in Ns:
    if str(N) in d:
        continue
    t = time.time()
    b, w, tt = J.exact(N, verbose=False)
    assert J.runs_value(w) == b and 0 < w < 2 ** N and w % 2
    d[str(N)] = dict(B4=b, witness=str(w), t=tt, secs=round(time.time() - t, 1))
    json.dump(d, open(f, 'w'), indent=0)
    print(f"B4({N}) = {b} (N+{b - N})  {time.time() - t:.1f}s", flush=True)
