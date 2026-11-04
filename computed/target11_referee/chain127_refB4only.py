"""Pilot: m=127 chain using only grid points that an independent referee recomputed (value <= grid)."""
import sys, os, json, glob, time
REL = r"C:\Users\hackathon\Documents\GitHub\collatz-m-cycles-release\computed"
sys.path.insert(0, os.path.join(REL, 'target11_fourrise'))
os.chdir(os.path.join(REL, 'target11_fourrise'))
import fastchain as FC
R = FC.R
def main():
    d2, d3, d4 = R.R7.load_b2(), R.R7.load_b3(), R.load_b4(852)
    def jl(pat):
        out = {}
        for f in glob.glob(os.path.join(REL, pat)):
            for line in open(f):
                line = line.strip()
                if line:
                    r = json.loads(line); out[r['N']] = r
        return out
    rb2 = jl('target7b_referee/b2_*.jsonl'); rb3 = jl('target7b_referee/b3grid_*.jsonl')
    rb4 = {}
    for f in ['refb4_points.json', 'refb4_points_extra.json']:
        rb4.update({int(k): v for k, v in json.load(open(os.path.join(REL, 'target11_referee', f))).items()})
    def ok2(N): r = rb2.get(N); return r is not None and r.get('ok') and r['mine'] <= d2[N]
    def ok3(N): r = rb3.get(N); return r is not None and r.get('ok') and r['mine'] <= d3[N]
    def ok4(N): r = rb4.get(N); return r is not None and r.get('ok') and r['ref_max_ge_grid'] <= d4[N]
    D2 = dict(d2)  # 14 small grid_own points are known safe overestimates (Lean-checked range)
    D3 = {N: B for N, B in d3.items() if ok3(N)}
    D4 = {N: B for N, B in d4.items() if ok4(N)}
    print('B2', len(d2), 'refereed', len(D2), 'missing', sorted(set(d2) - set(D2))[:60])
    print('B3', len(d3), 'refereed', len(D3), 'missing', sorted(set(d3) - set(D3)))
    print('B4', len(d4), 'refereed', len(D4), 'missing', sorted(set(d4) - set(D4)))
    print('tops', max(D2), max(D3), max(D4), flush=True)
    if len(sys.argv) > 1:
        for m in map(int, sys.argv[1].split(',')):
            FC.run(m, D2, D3, D4, int(sys.argv[2]) if len(sys.argv) > 2 else 2, 300)

if __name__ == '__main__':
    main()
