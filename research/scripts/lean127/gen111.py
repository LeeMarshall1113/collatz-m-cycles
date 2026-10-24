"""m = 111: B3 points 498, 522 (AllTriples parts + grid3_111), grid111 = grid110, data111 checked with
MCycleChain3D (uOKD: the 80-digit log2 3 bound in the shape certificate).  Wraps mcycle109/gen109.py."""
import os, sys, glob, threading
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle109'))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle107'))
import gen109 as G
import b3mods
L, GM = G.L, G.L.G
OUT = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'Collatz'))
DHI80 = F(158496250072115618145373894394781650875981440769248106045575265454109822779435857, 10 ** 80)
NEW3 = [(498, 512), (522, 539)]
PARTS3 = {498: 10, 522: 12}
G.GRID3 = G.GRID3 + NEW3
G.B2NEW[111] = G.B2NEW[109] + [(247533, 247549), (384012, 384028), (403213, 403231), (647476, 647493)]

def room80(m, K, P, m2, N, M):
    return (F(P) - K * DHI80) * GM.L2 - F(1, 2**N - 1) - F(m2 - 1, 2**M - 1)
def u_ok80(m, K, P, m2, N, M, Ub):
    if not (1 <= m2 <= m and N >= 1 and M >= 1):
        return False
    if not (N * m * GM.Ghi(m2) <= m2 * K and M * m * (1 + GM.Ghi(m2 - 1)) <= m2 * K):
        return False
    if not (K * DHI80 <= P):
        return False
    r = room80(m, K, P, m2, N, M)
    return r > 0 and F(m - m2) <= Ub * r
L.room, L.u_ok = room80, u_ok80          # the shape certificate only; the walk keeps DLO/DHI (50 digits)
import inspect
_src = inspect.getsource(L.u_cert).replace("G.DHI", "DHI80")
_ns = dict(vars(L)); _ns["DHI80"] = DHI80; _ns["room"] = room80; _ns["u_ok"] = u_ok80
exec(_src, _ns)
L.u_cert = _ns["u_cert"]

def b3():
    joins = {N: b3mods.part_modules(OUT, N, B, G.E1, PARTS3[N], "lean127/gen111.py") for N, B in NEW3}
    b3mods.grid_module(OUT, "grid3_111", "MCycleGrid3_111", G.GRID3, ["MCycleGrid3_107"], joins,
                       "The three-rise grid for `m = 111`")

def post():
    for p in glob.glob(os.path.join(OUT, "MCycle111*.lean")):
        s = open(p, encoding="utf-8").read()
        for a, b in [("import Collatz.MCycleChain3\n", "import Collatz.MCycleChain3D\n"), ("MCycleGrid3_107", "MCycleGrid3_111"),
                     ("grid3_107", "grid3_111"), ("certsOK3", "certsOK3D"), ("mOK3", "mOK3D")]:
            s = s.replace(a, b)
        open(p, "w", encoding="utf-8").write(s)
    open(os.path.join(OUT, "MCycleGrid111.lean"), "w", encoding="utf-8").write(
        "import Collatz.MCycleGrid110\n\n/-!\n# Two-rise grid `grid111` (= `grid110`)\n-/\n\nnamespace Collatz\n\n"
        "def grid111 : List (ℕ × ℕ) := grid110\n\ntheorem grid111_ok : ∀ e ∈ grid111, TwoRiseBound e.1 e.2 := grid110_ok\n\nend Collatz\n")

def main():
    b3()
    sys.argv = [sys.argv[0], OUT, '111']
    G._main()
    post()

if __name__ == "__main__":
    sys.setrecursionlimit(3000000); threading.stack_size(250 * 2 ** 20)
    th = threading.Thread(target=main); th.start(); th.join()
