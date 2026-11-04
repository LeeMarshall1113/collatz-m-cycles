"""Gap-fill driver for the referee: refshapes.main_stream(m) (unmodified: own floor-sum survivor count per
piece, candidates tested against it, own refchain screen of every survivor, exact own chain on the open and
top-50 shapes), with refshapes.HERE pointed at this folder so that its pickle refshapes_<m>.pkl is written
here and not into target11_referee.  (The B4 snapshot path HERE/../target11_fourrise/... resolves the same.)
Note: main_stream's line "candidates N (fastchain reported 5291301 at m=127)" has that m=127 figure hard-coded.
usage: python ref_gap.py m [m ...]"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'target11_referee'))
import refshapes as RS   # noqa: E402
RS.HERE = HERE
if __name__ == '__main__':
    for m in map(int, sys.argv[1:]):
        RS.main_stream(m)
