"""run refb4.search at V = g(N) (snapshot grid value) for the binding points; result: max value found
(= exact B4(N) iff found nonempty: all n with value >= g(N) are found).  writes refb4_points.json"""
import sys, json, os, time
import refb4 as B
snap = json.load(open(os.path.join('..', 'target11_fourrise', 'b4_grid_snapshot_le852.json')))
pts = [int(x) for x in sys.argv[1].split(',')]
th = int(sys.argv[2]) if len(sys.argv) > 2 else 4
outf = sys.argv[3] if len(sys.argv) > 3 else 'refb4_points.json'
res = json.load(open(outf)) if os.path.exists(outf) else {}
for N in pts:
    if str(N) in res:
        continue
    g = snap[str(N)]['B4']
    t = time.time()
    f, st = B.search(N, g, th)
    best = max(f.values()) if f else None
    res[str(N)] = dict(grid=g, ref_max_ge_grid=best, n_found=len(f), ok=(best == g),
                       witness=str(max(f, key=f.get)) if f else None, secs=round(time.time() - t, 1),
                       items=st.get('items'), joinhits=st.get('joinhits'))
    json.dump(res, open(outf, 'w'), indent=1)
    print(f"N={N}: grid {g}, referee B4 = {best} -> {'AGREE' if best == g else 'DISAGREE'}  ({time.time()-t:.0f}s)", flush=True)
