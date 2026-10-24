# computed/: reproducing m <= 127 (NOT formally verified)

Python programs and certificate summaries for the three-rise result (every shape closed for m <= 121) and the
four-rise extension (m <= 127). The mathematics is in `../METHOD.md`. Everything here was written by an AI (Claude,
Anthropic) under Lee Marshall's direction; the referee code is likewise AI-written. **Nothing in this directory is
kernel-checked.** The Lean-verified result (m <= 110) does not depend on it.

## Layout

The directory names are those of the development repository; the scripts find each other with relative paths
(`../target7_threerise`, ...), so keep the layout. Run each script from its own directory.

| Directory | Content |
|---|---|
| `target1a/chain/` | `common.py` (constants, interval logs, Theorem-21 filter `survives`), `shapes.py`, `chain.py`, `tworise.py`, `grid_own.json` (B2 grid, N <= 66,903) |
| `target1a/referee_tworise/` | `tworise.py` (an independently written B2 checker) |
| `target7_threerise/` | `chain3.py` (three-term chain), `b3.py` (B3 helpers), `grid3_p0/p1.json` (84 exact B3 points, N = 70..3300), `b2_extra.json`, `brute.py`, `test_b3.py` |
| `target10_rrise/` | `chainr.py` (r-term chain), `b4_grid.json` (36 early B4 points), `hard.txt` (least surviving K per m) |
| `target7b_push/` | `b3join.py` (exact B3 by a join), `b2fast.py` (exact B2), `fastshapes.py` (exact shape enumeration), `run7b.py` (all shapes through the three-term chain), `grid7b.py`, `b2_new_g*.json` (43 B2 points to 1,039,710), `b3_new_g*.json` (42 B3 points to 38,243), `final_runs.out` (results m = 105..121), `cmp_m10*.out`, `grid_validate.out`, `test_join.py` |
| `target11_fourrise/` | `b4join.py` (exact B4), `grid4.py`, `adapt.py` (adaptive B4 points), `run11.py` / `fastchain.py` (all shapes, four-term chain), `b4_grid_snapshot_le852.json` (117 B4 points, N = 72..852), `b4_new_*.json`, `chain_126_final.out`, `chain_127_final.out`, `test_b4*.out` |
| `target11_referee/` | independent referee for the four-rise part: `refb4.py` (own B4), `refchain.py` (own chain), `refshapes.py` (own survivor count and screen), `sample50.py`, `binding.py`, logs and recomputed points |
| `target7b_referee/` | independent referee for the three-rise part: `myb2.py`, `myb3.py`, `myshapes.py`, `mychain.py`, logs, recomputed grids |
| `target7c_proofs/` | `PROOFS.md` (written proofs of Theorem 1, Lemma 3S, r-step lemma, chain theorem; second referee), `b3crt.py`, `enum7c.py`, `bulk.py`, `indep.py`, `chain_all.py`, `bulk121.out`, `surv_m110.txt` |

## Setup

Python 3 with `numpy`, `numba`, `gmpy2`, `mpmath` (used: Python 3.14.0, mpmath 1.3.0, numpy 2.5.4, numba 0.68.0, gmpy2
2.3.2). **Always set `MPMATH_NOGMPY=1`**: with gmpy2 installed, mpmath hands `mpz` to `Fraction` and the shape code
crashes on Python 3.14. (The original runs went through a launcher that only added a site-packages path; not needed
here.)

```sh
export MPMATH_NOGMPY=1
```

## Steps

Runtimes are from the original runs (a shared 8-core Windows machine, often loaded), unless marked "timed here".
Peak memory was not recorded for the chain runs; the referee B4 jobs peaked at about 1.2 GB. The expected output of
each step is in the `.out`/`.log` file named.

### 1. Quick sanity checks (seconds; all timed here and matching)

```sh
cd target11_fourrise && python fastchain.py 110 --procs 1 --b4top 852      # ~4 s
#   m=110: worst exact ratio 0.000396 at K=27444133206411171953 ... failures 0; CLOSED
cd ../target7b_push && python run7b.py 110 --procs 1                         # ~10 s
#   m=110: worst ratio 0.00628 at K=27444133206411171953; failures 0; CLOSED     (three-rise only)
cd ../target7c_proofs && python bulk.py 110 surv_m110.txt 1                  # ~15 s, independent referee chain
#   m=110 shapes 2113 ... FAILURES 0, ratio<=0.006283 at K=27444133206411171953
cd ../target11_fourrise && python test_b4.py 4 14                            # ~16 s, B4 join vs brute force
#   ALL OK      (the full validation is `python test_b4.py 4 22`, and `... 4 22 2` to force paging; see test_b4*.out)
```

### 2. All shapes for m <= 121 with B2 + B3 (three-rise)

```sh
cd target7b_push && python run7b.py 121 --procs 3        # ~20 min enumeration + ~11 min chain on 3 processes
# expected (final_runs.out):  m=121: worst ratio 0.99629 at K=27444133206411171953; failures 0; CLOSED
# 334,036 shapes. m = 122 fails at 1.579.
```

Independent bulk check: the second referee's own chain (exact rationals, own log bounds) run over the survivor list
dumped from `fastshapes` (about 18 min on 3 processes; the survivor *set* itself was confirmed independently by the
first referee's enumerator and, at m = 104 and 110, by `enum7c.py`):

```sh
cd target7c_proofs && python dump_surv.py 121 && python bulk.py 121 surv_m121.txt 3
# expected (bulk121.out):  m=121 shapes 334036 ... FAILURES 0 ; ratio<=0.996289 at K=27444133206411171953
python enum7c.py 110 19495996922966119759541821     # independent enumeration, m = 110 Kceil: 2113 survivors,
                                                    # identical to surv_m110.txt (cmp_m110.out)
```

(`dump_surv.py` imports `../target7b_push/fastshapes.py`. The 18 MB m = 121 survivor file is not included.)

### 3. All shapes for m <= 127 with B2 + B3 + B4 (four-rise)

```sh
cd target11_fourrise && python fastchain.py 127 --procs 3 --b4top 852      # enumeration ~106 s + screen ~420 s on 3 processes
# expected (chain_127_final.out):
#   m=127 Kceil=5.5609e+28 candidates=5291301 screened-closed=5291298 exact-needed=0 failures=0 B4top=852
#   m=127: worst exact ratio 0.996295 at K=27444133206411171953 use={1: 68, 2: 15, 3: 26, 4: 17}
#          maxN={2: 986691, 3: 35583, 4: 830} (worst valid as global max: True) ... CLOSED
python fastchain.py 126 --procs 3 --b4top 852   # 0.628592, 3,338,831 candidates (chain_126_final.out)
```

0.996295 is obtained from the grid snapshot minus the point N = 510; with the full 117-point snapshot the ratio is
0.9962878 (a reporting nit noted by the referee). Both are below 1. `run11.py m` is the slow, unscreened version of the
same test.

### 4. Regenerating the rise-bound tables (hours; not re-run for this release)

Each point is exact and its maximiser is re-simulated with the Collatz map before it is written.

```sh
cd target7b_push
python grid7b.py b3 TAG 38243            # B3(N): about 50 min on a loaded machine for N = 38,243
python grid7b.py b2 TAG 1039710          # B2(N): minutes to an hour per point at this size
cd ../target11_fourrise
NUMBA_NUM_THREADS=4 GRID=$PWD/b4_new_TAG.json python grid4.py 852   # B4(852): ~30 min on 4 threads (132 s at 472, 885 s at 757)
python adapt.py ...                       # the 70 adaptive B4 points for the hard shapes (see METHOD.md section 7)
```

Validation of the join algorithms against brute force and exhaustive enumeration: `target7b_push/test_join.py`
(`grid_validate.out`: all 84 old B3 values reproduced, 0 mismatches), `target11_fourrise/test_b4.py`
(`test_b4.out`, `test_b4_paged.out`).

### 5. The referees (for the record; expensive)

* Four-rise referee, own B4: `cd target11_referee && python run_b4pts.py 509,510,532 4 refb4_points.json`
  (about 1 minute per point at N ~ 500, about 9 minutes at N = 852); results `b4pts.log`, `b4extra.log`: the referee's
  `B4(N)` equals the grid value at all 72 points checked. Own survivor count at m = 127 (`python refshapes.py 127`,
  `refshapes_127.log`): 5,291,294 survivors, all among the 5,291,301 candidates. Own chain on 51 shapes
  (`python sample50.py 127`, `sample50_127.out`): 51/51 exactly equal.
* Three-rise referees: `target7b_referee/` (recomputed all 84 + 42 B3 points and 41 new B2 points; logs
  `b3grid_*.log`, `b2_*.log`) and `target7c_proofs/` (`PROOFS.md`; `b3crt.py` checks B3(73) = 85 and B3(117) = 130
  by a different method; `enum7c.py` reproduces the survivor sets at m = 104, 110).
  Not re-run for this release.

## Referee verdicts (summary)

* **m <= 121, three-rise:** two independent referee sessions plus a bulk re-check: no error found. Worst ratio
  0.996288873 at K = 27,444,133,206,411,171,953; 0 failures over 334,036 shapes. Presentation gaps (G1-G5 in
  `PROOFS.md`), none fatal.
* **m = 122..127, four-rise:** one independent referee session (own B4 code, own chain, own survivor count): no error
  found; 72 B4 points recomputed with 0 mismatches; screen proven valid. **The B4 part had only this one referee**, and
  Theorem R for r = 4 has no independently written proof (only an independent implementation validated against brute
  force for N <= 22).
* Margins are thin (0.37% at m = 127), and the argument needs the B2/B3/B4 tables to be exact or over-estimates
  (see `../METHOD.md` section 9).

## Not included

The 18 MB survivor list for m = 121 (regenerate with `dump_surv.py 121`), pickles of referee shape sets, per-point grid logs,
and the broker/launcher scripts of the development machine.
