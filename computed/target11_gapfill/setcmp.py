"""Set comparison of the two survivor tests over the fastshapes candidate list, at each m.

Candidates: fastchain.candidates' exact recipe (fastshapes.merge(intervals), box_points with
eta = L/L2LO (1 + 1e-9), 1 <= K < Kceil), streamed interval by interval (as refshapes.main_stream).
For every candidate (K, p) two survivor tests are evaluated:
  * REF : refshapes' own exact test (e = p - K delta bracketed at 2^-320 against the referee's piece
          eta brackets; refshapes.pieces / eta_brackets, unmodified).  An ambiguous bracket is counted.
  * FAST: common.survives(m, K, p), the test fastshapes.surviving applies.  survives() calls
          lam_bound(m, K), which depends on K only through the tuple NM(m, m2, K), m2 = 1..m; NM is
          nondecreasing in K.  So for each referee piece [Ka, Kb) that holds candidates, the tuple is
          computed with common.NM at Ka and at Kb - 1; if equal (asserted), lam_bound is constant on the
          piece and common.lam_bound(m, Ka) is used for every K in it.  The rest is survives' own body:
          p > K DLO and p - K DHI < lam / L2LO (exact Fractions).
Output: candidates, |REF|, |FAST|, |REF & FAST|, REF-only, FAST-only, sha256 of each survivor list
(in increasing K), and the per-piece floor-sum count total (refshapes' independent count).
usage: python setcmp.py m [m ...]
"""
import sys, os, time, bisect, hashlib
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
REL = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(REL, 'target11_referee'))
sys.path.insert(0, os.path.join(REL, 'target11_fourrise'))
import refshapes as RS     # noqa: E402
import fastchain as FC     # noqa: E402
fs, C = FC.fs, FC.C


def run(m):
    t0 = time.time()
    Kceil = fs.shapes.rhin_ceiling(m)
    iv = fs.merge(fs.intervals(m, Kceil))
    pcs = RS.pieces(m, Kceil)
    starts = [a for a, _, _ in pcs]
    Es = [RS.eta_brackets(l) for _, _, l in pcs]
    cnt_exact, bad = 0, 0
    for (Ka, Kb, l), (Elo, Ehi) in zip(pcs, Es):
        c1 = RS.count_piece(Ka, Kb, Elo); c2 = RS.count_piece(Ka, Kb, Ehi)
        if len(set(c1 + c2)) != 1:
            bad += 1
        cnt_exact += c2[1]
    print(f"m={m}: Kceil={Kceil}; {len(iv)} merged intervals; referee pieces {len(pcs)}; floor-sum survivor count "
          f"{cnt_exact}; ambiguous pieces {bad} ({time.time() - t0:.0f}s)", flush=True)
    lamc = {}
    st = dict(cand=0, ref=0, fast=0, both=0, ref_only=0, fast_only=0, amb=0, pieces_used=0)
    h_ref, h_fast = hashlib.sha256(), hashlib.sha256()
    ex_ref, ex_fast = [], []
    t1 = time.time()
    for Ka_, Kb_, L in iv:
        eta = Fr(L) / C.L2LO * (1 + Fr(1, 10 ** 9))
        pts = sorted(set(p for p in fs.box_points(Ka_, Kb_, eta)[0] if 1 <= p[0] < Kceil))
        st['cand'] += len(pts)
        for K, p in pts:
            i = bisect.bisect_right(starts, K) - 1
            elo = p * RS.Q - K * RS.D_A_HI
            ehi = p * RS.Q - K * RS.D_A_LO
            Elo, Ehi = Es[i]
            if elo > 0 and ehi < Elo:
                r = True
            elif ehi <= 0 or elo >= Ehi:
                r = False
            else:
                st['amb'] += 1; r = False
            lam = lamc.get(i)
            if lam is None:
                a, b = pcs[i][0], pcs[i][1] - 1
                ta = tuple(C.NM(m, m2, a) for m2 in range(1, m + 1))
                tb = tuple(C.NM(m, m2, b) for m2 in range(1, m + 1))
                assert ta == tb, (m, a, b)
                lam = lamc[i] = C.lam_bound(m, a) / C.L2LO
                st['pieces_used'] += 1
            f = (p > K * C.DLO) and (p - K * C.DHI < lam)
            line = f"{K} {p}\n".encode()
            if r:
                st['ref'] += 1; h_ref.update(line)
            if f:
                st['fast'] += 1; h_fast.update(line)
            if r and f:
                st['both'] += 1
            elif r:
                st['ref_only'] += 1
                if len(ex_ref) < 10: ex_ref.append((K, p))
            elif f:
                st['fast_only'] += 1
                if len(ex_fast) < 10: ex_fast.append((K, p))
    same = st['ref_only'] == 0 and st['fast_only'] == 0 and st['amb'] == 0 and h_ref.digest() == h_fast.digest()
    print(f"m={m}: candidates {st['cand']}; REF survivors {st['ref']}; FAST survivors {st['fast']}; both {st['both']}; "
          f"REF-only {st['ref_only']} {ex_ref}; FAST-only {st['fast_only']} {ex_fast}; ambiguous {st['amb']}; "
          f"lam pieces {st['pieces_used']} ({time.time() - t1:.0f}s)", flush=True)
    print(f"m={m}: sha256 REF {h_ref.hexdigest()}", flush=True)
    print(f"m={m}: sha256 FAST {h_fast.hexdigest()}", flush=True)
    print(f"m={m}: floor-sum count {cnt_exact} == REF {st['ref']}: {cnt_exact == st['ref']}; "
          f"SETS {'IDENTICAL' if same else 'DIFFER'}", flush=True)


if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        run(m)
