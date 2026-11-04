"""Independent (referee-code) check for m >= 128.  Drives the referee's own code UNMODIFIED, with two injections:
  * refchain.load_grids additionally loads this folder's doubly computed points (b2_new_*.json, b3_new_*.json);
  * fastshapes.box_points -> shapes13.box_points (endpoint y-window, F1), used by the candidate stream of
    refshapes.main_stream and of target11_gapfill/setcmp.py.
Everything else (own Rhin check, floor-sum survivor count, own survivor test, own chain refchain.chain/ratio with
the 117-point B4 snapshot, set comparison with sha256) is the referee's / gap-fill's code.
usage: python ref13.py hard m [m ...]      refchain ratio of the hard shape (and hard.txt's 8 least K survivors)
       python ref13.py shapes m [m ...]    refshapes.main_stream(m)   (pickle refshapes_<m>.pkl written here)
       python ref13.py setcmp m [m ...]    target11_gapfill/setcmp.run(m)"""
import sys, os, json, glob, math
HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import shapes13                                   # noqa: E402
shapes13.patch()
sys.path.insert(0, os.path.join(COMP, 'target11_referee'))
import refchain as RC                             # noqa: E402
import refshapes as RS                            # noqa: E402

_orig = RC.load_grids


def extra(kind):
    d = {}
    for f in sorted(glob.glob(os.path.join(HERE, f'b{kind}_new_*.json'))):
        for k, v in json.load(open(f)).items():
            d[int(k)] = v[f'B{kind}']
    return d


def load_grids(b4file=None):
    tabs = _orig(b4file)
    for r in (2, 3):
        d = dict(tabs[r].d)
        d.update(extra(r))
        tabs[r] = RC.Table(d)
    return tabs


RC.load_grids = load_grids
RS.RC.load_grids = load_grids
RS.HERE = HERE
SNAP = os.path.join(COMP, 'target11_fourrise', 'b4_grid_snapshot_le852.json')

if __name__ == "__main__":
    a = sys.argv[1:]
    mode, ms = a[0], list(map(int, a[1:]))
    import fastshapes
    assert fastshapes.box_points is shapes13.box_points
    if mode == 'hard':
        tabs = load_grids(SNAP)
        print("extra B2", extra(2), "extra B3", extra(3), flush=True)
        rows = sorted(tuple(map(int, l.split()[:3])) for l in open(os.path.join(COMP, 'target10_rrise', 'hard.txt'))
                      if not l.startswith('#'))
        for m in ms:
            for K, p, e in [r for r in rows if r[2] <= m][:8]:
                r, tr = RC.ratio(m, K, p, tabs)
                print(f"m={m} K={K} p={p} refchain ratio {'none' if r is None else '%.7f' % float(r)}", flush=True)
    elif mode == 'shapes':
        for m in ms:
            RS.main_stream(m)
    elif mode == 'setcmp':
        sys.path.insert(0, os.path.join(COMP, 'target11_gapfill'))
        import setcmp
        assert setcmp.fs.box_points is shapes13.box_points
        for m in ms:
            setcmp.run(m)
