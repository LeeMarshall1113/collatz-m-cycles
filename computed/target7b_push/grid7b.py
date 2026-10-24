"""grid driver: python grid7b.py b3|b2 TAG N [N ...]  -> b3_new_TAG.json / b2_new_TAG.json
Each value exact (asserted) with its witness re-simulated literally."""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
kind, tag = sys.argv[1], sys.argv[2]
f = os.path.join(HERE, f"{kind}_new_{tag}.json")
d = json.load(open(f)) if os.path.exists(f) else {}
for N in map(int, sys.argv[3:]):
    if str(N) in d:
        continue
    t = time.time()
    if kind == 'b3':
        import b3join as J
        r = J.b3_exact(N)
        rec = dict(N=N, B3=r['B3'], exc=r['B3'] - N, sigma=list(r['arg']), ks=r['witness_ks'],
                   t=r['t'], Kmax=r['Kmax'], nfound=r['nfound'], ncand=r['ncand'], nmatch=r['nmatch'],
                   secs=round(time.time() - t, 1))
    else:
        import b2fast
        B, arg, nc, secs = b2fast.b2(N)
        ws = b2fast.witness(N, arg)
        assert ws == B
        rec = dict(N=N, B2=B, exc=B - N, arg=list(arg), secs=round(secs, 1))
    d[str(N)] = rec
    json.dump(d, open(f + '.tmp', 'w'), indent=0)
    os.replace(f + '.tmp', f)
    print(rec, flush=True)
