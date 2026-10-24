"""Emit the Lean modules for m = 106, 107 with the three-rise chain (MCycleChain3.lean); from gen105.py.

usage: python gen105.py OUTDIR m [m ...]
Per m: MCycle<m>Def.lean (data<m>), MCycle<m>Walk<j>.lean (the Farey walk in pieces, WalkSplit.lean),
MCycle<m>Shapes.lean, MCycle<m>Certs<j>.lean (certsOK3 in chunks), MCycle<m>Data.lean (mOK3 and
no_<m>_cycle_of_floor). Also MCycleThreeRise105.lean (AllTriples kernel checks) and
MCycleGrid3_107.lean (grid3_107). The walk split follows mcycle103_split/{tree,keys,gen_split}.py."""
import os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle105'))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle107'))
sys.setrecursionlimit(1000000)
import chain3 as C3
G, L = C3.G, C3.L

B2NEW = {108: [(97951, 97965)], 109: [(97951, 97965), (151960, 151978)]}
GRID3 = [(79, 88), (122, 135), (203, 216), (325, 340)]
OLD3 = {79, 122}                     # AllTriples already in MCycleThreeRise105.lean
PARTS = {203: 1, 325: 3}             # independent modules per N (built two at a time)
E1 = 16
R = int(os.environ.get("CHAIN_R", "500"))          # single steps per walk_wchain key
PER = int(os.environ.get("WALK_PER", "6000"))      # walk steps per module
CH = int(os.environ.get("CERT_CHUNK", "5"))
QM = int(os.environ.get("CERT_PER_MOD", "4"))
TRIPLES_PER_CHUNK = int(os.environ.get("TRIPLES_PER_CHUNK", "20000"))


def W3(N, B):
    return 2 * B + 2 * E1 + 64


def lit(sh):
    return "([] : List (ℕ × ℕ))" if not sh else "[" + ", ".join(f"({k}, {p})" for k, p in sh) + "]"


# ---------------- the B3 kernel checks ----------------
def threerise_module(out, check=True):
    import threerise_mirror as TM
    import b3mods
    joins = {}
    for N, B in GRID3:
        if N in OLD3:
            continue
        if check:
            assert TM.all_triples(N, B, E1, W3(N, B)) and not TM.all_triples(N, B - 1, E1, W3(N, B))
        joins[N] = b3mods.part_modules(out, N, B, E1, PARTS[N], "mcycle107/gen107.py")
    b3mods.grid_module(out, "grid3_107", "MCycleGrid3_107", GRID3, ["MCycleThreeRise105"], joins,
                       "The three-rise grid for `m = 106, 107`")

# ---------------- the walk tree ----------------
def build_tree(P):
    st = [(e[0],) + (0,) * 5 + (e[6],) for e in P['st']] + [(P['Ks'],) + (0,) * 5 + (P['stall'][5],)]
    Kc, Km = P['Kceil'], P['Ks']
    nodes = []
    # iterative post-order construction
    a, b, c, d = P['abcd']
    root = [None]
    stack = [('enter', P['fuel'], a, b, c, d, root, 0)]
    while stack:
        item = stack.pop()
        if item[0] == 'enter':
            _, fuel, a, b, c, d, slot, k = item
            assert fuel > 0
            i = len(nodes); nodes.append(None); slot[k] = i
            f, e = b + d, a + c
            if Kc <= f:
                nodes[i] = dict(fuel=fuel, abcd=(a, b, c, d), kind='stop', ch=[], mu=[], sh=[])
                continue
            ep = G.eps_at(max(f, Km), st)
            assert ep is not None
            if F(e, f) <= G.DLO:
                ch = [None]; nodes[i] = dict(fuel=fuel, abcd=(a, b, c, d), kind='lo', ch=ch, mu=[])
                stack.append(('exit', i)); stack.append(('enter', fuel - 1, e, f, c, d, ch, 0))
            elif G.DHI + ep <= F(e, f):
                ch = [None]; nodes[i] = dict(fuel=fuel, abcd=(a, b, c, d), kind='hi', ch=ch, mu=[])
                stack.append(('exit', i)); stack.append(('enter', fuel - 1, a, b, e, f, ch, 0))
            else:
                mu = G.mults(st, Kc, Km, e, f)
                ch = [None, None]; nodes[i] = dict(fuel=fuel, abcd=(a, b, c, d), kind='mid', ch=ch, mu=mu)
                stack.append(('exit', i))
                stack.append(('enter', fuel - 1, e, f, c, d, ch, 1))
                stack.append(('enter', fuel - 1, a, b, e, f, ch, 0))
        else:
            i = item[1]; n = nodes[i]
            n['sh'] = n['mu'] + sum((nodes[j]['sh'] for j in n['ch']), [])
    return nodes, root[0]


def make_keys(nodes, root):
    keys = []
    stack = [('seg', root)]
    while stack:
        it = stack.pop()
        if it[0] == 'emit':
            keys.append(it[1]); continue
        i = it[1]; n = nodes[i]
        if n['kind'] == 'stop':
            keys.append(dict(i=i, t='stop')); continue
        if n['kind'] == 'mid':
            stack.append(('emit', dict(i=i, t='mid', l=n['ch'][0], r=n['ch'][1])))
            stack.append(('seg', n['ch'][1])); stack.append(('seg', n['ch'][0]))
            continue
        j, steps = i, 0
        while nodes[j]['kind'] in ('lo', 'hi') and steps < R:
            j = nodes[j]['ch'][0]; steps += 1
        stack.append(('emit', dict(i=i, t='chain', n=steps, to=j)))
        stack.append(('seg', j))
    return keys


# ---------------- the data modules ----------------
def write_m(out, P, nodes, root, keys):
    m = P['m']; GT = str(m); GN = f'grid{m}'
    D = f"data{m}"
    W = f"walk {D}.pairs {D}.Kceil {D}.Ks"
    IMP = f"(st := {D}.pairs) (Kc := {D}.Kceil) (Km := {D}.Ks)"
    steps, Ks, stall, st, certs = P['steps'], P['Ks'], P['stall'], P['st'], P['certs']
    a, b, c, d = P['abcd']
    with open(os.path.join(out, f"MCycle{m}Def.lean"), "w", encoding="utf-8") as f:
        f.write("import Collatz.MCycleChain3\nimport Collatz.WalkSplit\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n")
        f.write(f"/-!\n# The exclusion data for `m = {m}` (three-rise chain)\n\n"
                f"Generated by `research/scripts/mcycle105/gen105.py`: the bootstrap at the floor `2⁷¹ + 1`\n"
                f"({len(steps)} steps, `K ≥ {Ks}`), the stair ({len(st)} entries), the Rhin ceiling\n"
                f"`K < {P['Kceil']}`, the Farey walk ({P['nodes']} nodes), {len(certs)} listed shape(s) with\n"
                f"their chain certificates (two-rise bounds from `{GN}`, three-rise from `grid3_107`).\n-/\n\n")
        f.write("namespace Collatz\n\n")
        boot = ",\n    ".join(L.lean_step(s_) for s_ in steps)
        stairs = ",\n    ".join(L.lean_stair_entry(e) for e in st)
        cs = ",\n    ".join(L.lean_cert(cc) for cc in certs)
        f.write(f"/-- The exclusion data for `m = {m}`. -/\ndef {D} : MData where\n")
        f.write(f"  boot := [{boot}]\n  Ks := {Ks}\n  root := {L.lean_step(stall)}\n")
        f.write(f"  ra := {a}\n  rb := {b}\n  rc := {c}\n  rd := {d}\n  stair := [{stairs}]\n")
        f.write(f"  Kceil := {P['Kceil']}\n  V := {P['V']}\n  cexp := {P['cexp']}\n  kexp := {P['kexp']}\n")
        f.write(f"  fuel := {P['fuel']}\n  certs := [{cs}]\n\nend Collatz\n")

    def lhs(i):
        n = nodes[i]; a, b, c, d = n['abcd']
        return f"{W} {n['fuel']} {a} {b} {c} {d}"

    def thm(k):
        i = k['i']; n = nodes[i]; Fu = n['fuel']; a, b, c, d = n['abcd']
        head = f"theorem w{m}_{i} : {lhs(i)} = {lit(n['sh'])} :="
        if k['t'] == 'stop':
            return f"{head}\n  walk_stop {IMP} {Fu - 1} (a := {a}) (c := {c}) (by decide +kernel)\n", 1
        if k['t'] == 'chain':
            j = k['to']; mm = nodes[j]; a2, b2, c2, d2 = mm['abcd']; s = k['n']
            assert mm['fuel'] == Fu - s and mm['sh'] == n['sh']
            return (f"{head}\n  (walk_wchain {IMP} {Fu - s} {s} (a := {a}) (b := {b}) (c := {c}) (d := {d})\n"
                    f"    (a' := {a2}) (b' := {b2}) (c' := {c2}) (d' := {d2}) (by decide +kernel)).trans w{m}_{j}\n"), s
        l, r = k['l'], k['r']
        e, g = a + c, b + d
        assert nodes[l]['abcd'] == (a, b, e, g) and nodes[r]['abcd'] == (e, g, c, d)
        return (f"{head} by\n  rw [walk_mid {IMP} {Fu - 1} (a := {a}) (b := {b}) (c := {c}) (d := {d}) (e := {e}) (g := {g})\n"
                f"    (by decide +kernel) rfl rfl, w{m}_{l}, w{m}_{r}]\n  decide +kernel\n"), 1

    mods, cur, cost = [], [], 0
    for k in keys:
        t, cc = thm(k)
        cur.append(t); cost += cc
        if cost >= PER:
            mods.append(cur); cur, cost = [], 0
    if cur:
        mods.append(cur)
    prev = f"MCycle{m}Def"
    for j, body in enumerate(mods):
        nm = f"MCycle{m}Walk{j + 1}"
        with open(os.path.join(out, nm + ".lean"), "w", encoding="utf-8") as f:
            f.write(f"import Collatz.{prev}\n\n/-!\n# The Farey walk of `{D}`, part {j + 1} of {len(mods)}\n\n"
                    f"Generated by `gen105.py` (`WalkSplit.lean`); each `decide +kernel` evaluates one node or\n"
                    f"one run of single steps.\n-/\n\nset_option Elab.async false\nset_option maxRecDepth 100000\n\nnamespace Collatz\n\n")
            f.write("\n".join(body))
            f.write("\nend Collatz\n")
        prev = nm
    sh = nodes[root]['sh']
    chunks = [sh[x:x + CH] for x in range(0, len(sh), CH)]
    nm = f"MCycle{m}Shapes"
    with open(os.path.join(out, nm + ".lean"), "w", encoding="utf-8") as f:
        f.write(f"import Collatz.{prev}\n\n/-!\n# The listed shapes of `{D}`, from the walk pieces, in chunks of {CH}\n-/\n\nset_option maxRecDepth 100000\n\n"
                f"namespace Collatz\n\n/-- The listed shapes (the value of `{D}.shapes`). -/\n"
                f"def shapes{m} : List (ℕ × ℕ) := {lit(sh)}\n\n"
                f"theorem {D}_shapes : {D}.shapes = shapes{m} := w{m}_{root}\n\n")
        for j, cch in enumerate(chunks):
            f.write(f"def shapes{m}_{j} : List (ℕ × ℕ) := {lit(cch)}\n\n")
        cat = " ++ ".join(f"shapes{m}_{j}" for j in range(len(chunks)))
        f.write(f"theorem shapes{m}_split : shapes{m} = {cat} := by\n  decide +kernel\n\nend Collatz\n")
    prev = nm
    cmods = []
    for q in range(0, len(chunks), QM):
        cm = f"MCycle{m}Certs{q // QM + 1}"
        with open(os.path.join(out, cm + ".lean"), "w", encoding="utf-8") as f:
            f.write(f"import Collatz.{prev}\n")
            if q == 0:
                f.write(f"import Collatz.MCycleGrid{GT}\nimport Collatz.MCycleGrid3_107\n")
            f.write(f"\n/-!\n# Certificates of the listed shapes of `{D}`, chunks {q}..{min(q + QM, len(chunks)) - 1}\n-/\n\n"
                    f"set_option Elab.async false\nset_option maxRecDepth 100000\n\nnamespace Collatz\n\n")
            for j in range(q, min(q + QM, len(chunks))):
                f.write(f"theorem certs{m}_{j} : certsOK3 {m} {L.S} {GN} grid3_107 {D}.certs shapes{m}_{j} = true := by\n"
                        f"  decide +kernel\n\n")
            f.write("end Collatz\n")
        prev = cm; cmods.append(cm)
    simps = ", ".join(f"certs{m}_{j}" for j in range(len(chunks)))
    with open(os.path.join(out, f"MCycle{m}Data.lean"), "w", encoding="utf-8") as f:
        f.write(f"import Collatz.{prev}\n\n/-!\n# No Collatz {m}-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)\n\n"
                f"`{D}` is in `MCycle{m}Def.lean`; its walk is evaluated in `MCycle{m}Walk1..{len(mods)}` and the\n"
                f"certificates in `MCycle{m}Certs1..{len(cmods)}`; `{D}_ok` assembles them into `mOK3`.\n-/\n\n"
                f"set_option maxRecDepth 100000\n\nnamespace Collatz\n\n"
                f"/-- The certificate check of all listed shapes, from the chunks. -/\n"
                f"theorem certs{m} : certsOK3 {m} {L.S} {GN} grid3_107 {D}.certs shapes{m} = true := by\n"
                f"  rw [shapes{m}_split]\n  simp only [certsOK3_append, {simps}, Bool.and_self]\n\n"
                f"theorem {D}_ok : mOK3 {m} {L.S} {GN} grid3_107 {D} = true := by\n"
                f"  unfold mOK3\n  rw [{D}_shapes, certs{m}, Bool.and_true]\n  decide +kernel\n\n"
                f"/-- **No Collatz {m}-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/\n"
                f"theorem no_{m}_cycle_of_floor (hR : RhinBound) {{x p : ℕ}} (hx : 0 < x) (hp : 0 < p)\n"
                f"    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :\n"
                f"    numLocalMin x p ≠ {m} := fun hm =>\n"
                f"  mOK3_sound hR {GN}_ok grid3_107_ok (by norm_num) {D}_ok hx hp hcyc hx1 hx2 hm hlow\n\n"
                f"end Collatz\n")
    print(m, "walk modules", len(mods), "keys", len(keys), "shapes", len(sh), "cert chunks", len(chunks),
          "cert modules", len(cmods), flush=True)


def _main():
        out = sys.argv[1]
        ms = list(map(int, sys.argv[2:]))
        for m in ms:
            g2 = C3.grid103() + B2NEW[m]
            P = L.plan_m(m, need_ns=False)
            for cc in P['certs']:
                assert C3.shape_ok3(m, g2, GRID3, cc)[0], (m, cc['K'])
            nodes, root = build_tree(P)
            assert sorted(set(nodes[root]['sh'])) == sorted(set((cc['K'], cc['P']) for cc in P['certs']))
            keys = make_keys(nodes, root)
            assert keys[-1]['i'] == root
            write_m(out, P, nodes, root, keys)

if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(3000000); threading.stack_size(250 * 2 ** 20)
    th = threading.Thread(target=_main); th.start(); th.join()
