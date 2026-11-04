"""[heuristic] Phase-sum rule for the reachable m, checked against the exact chain on synthetic grids.
    m* ~= 1 + L_1 + sum_{r=2..R} L_r + c,   L_r = log_delta(T_r / x0),   L_1 = log_delta(K (delta-1)/delta / x0)
T_r = top of the B_r grid, x0 = log2 Ub of the hard shape (~ K_B + 0.85 with Barina's 2^K_B), K = hard-shape K.
Derivation: in phase r the chain grows by delta per r steps, so phase r takes r log_delta(T_r/T_{r+1}) steps;
the final delta phase must stop where Y (delta/(delta-1)) ~ K.  Telescoping gives the sum.
usage: python formula.py"""
import math, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explore as E, trace as T     # noqa: E402

D = math.log2(3)
x0 = 71.85
K = T.HARD


def Lr(Tr):
    return math.log(Tr / x0) / math.log(D)


def pred(tops):
    return 1 + Lr(K * (D - 1) / D) + sum(Lr(t) for t in tops.values())


if __name__ == "__main__":
    cases = [dict(), dict(t2=1700000), dict(t2=2700000), dict(t2=4500000), dict(t3=60000), dict(t3=95000),
             dict(t4=1400), dict(t4=2200), dict(b5=150), dict(b5=300), dict(b5=300, t4=1400, t3=90000),
             dict(t2=4500000, t3=95000, t4=2200, b5=300)]
    for kw in cases:
        tops = {2: kw.get('t2', 1039710), 3: kw.get('t3', 38243), 4: kw.get('t4', 852)}
        if 'b5' in kw:
            tops[5] = kw['b5']
        m, r, r1, used = E.last_m(E.scen(**kw), hi=200)
        # continuous m: interpolate with ratio growth delta per m
        mc = m + math.log(1 / r) / math.log(D)
        print(f"{str(kw):45s} chain last m={m} (continuous {mc:.2f})  rule 1+sum L = {pred(tops):.2f}  diff {mc - pred(tops):+.2f}")
