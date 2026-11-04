# target11_gapfill: closing the record gaps for m = 112..127

Runs on 2026-11-03, 10:02-11:03 pm EST (2026-11-04 03:02-04:03 UTC). Every run was single-process and
single-thread, sequential, under compute-broker leases `collatz-m112-126-4467`, `-4468` and `-4474` (lease logs
`batch*_lease.log`, peak job commit 0.75 GB). AI-written (Claude) for Lee Marshall; nothing here is kernel-checked.

This addresses the referee's finding F3 (`../target11_referee/SHAPES-independent-proof.md`) and the "single
implementation" items listed there. m <= 111 is Lean-proved, and m = 114 and 116..121 close in
`../target7b_push/final_runs.out`.

## Search for existing logs (both repositories)

I found no chain log for m = 112, 113, 115, 122, 123 or 124 under any name. `collatz-loop/research/target7_threerise/
run3_m111_x.out` and `run3_m112_x.out` exist but are empty (0 bytes). `target7b_push/WRITEUP.md` says 111-113 and
115 "closed in earlier runs on sub-grids", but no output was kept. `target11_fourrise/WRITEUP.md` cites a
`chain_explore` run for 122-124, and no file of that name exists. The m = 125 log is
`collatz-loop/research/target11_fourrise/chain_757.out` (B4 grid to 757, not restricted to doubly computed points).

## What was run

| Script (this folder) | What it does |
|---|---|
| `fc_gap.py` | `fastchain.run` over **all** fastshapes candidates, using the grid selection of `../target11_referee/chain127_refB4only.py` (unmodified, imported): all 155 B2 points, 126 refereed B3 points, and only the **72 B4 points the referee recomputed** (value <= grid). `multiprocessing.Pool` is replaced by an in-process serial map. Logs: `fc_gap_112-124.log`, `fc_gap_125-126.log`. |
| `ref_gap.py` | `refshapes.main_stream(m)`, unmodified, with `HERE` redirected here so that its pickle goes in this folder. It runs the referee's own floor-sum survivor count per piece, the candidates' own exact survivor test, the own refchain screen of **every** survivor (B2+B3 and B2+B3+B4, 117-point snapshot), and the exact own chain on every open and top-50 shape. Logs: `refshapes_12{2..6}.log`, `.pkl`. The log text "(fastchain reported 5291301 at m=127)" is hard-coded in refshapes and should be ignored. |
| `setcmp.py` | **Set** comparison over the candidate list. For every candidate it evaluates the referee's survivor test and `common.survives` (the test `fastshapes.surviving` applies). `lam_bound` is cached per referee piece, and its constancy is asserted through `common.NM` at both ends of the piece. It reports the disagreements in each direction and the sha256 of both survivor lists. Logs: `setcmp_112-126.log`, `setcmp_113-115-127.log`. |

## Results

Candidates = fastshapes lattice points (fastchain). Survivors = Theorem-21 survivors. The referee's floor-sum
count equals the number of candidates passing its own test in **every piece** (0 mismatches, 0 ambiguous), so
referee survivors ⊆ fastshapes candidates at every m. The set match column compares the referee's set with
`common.survives` element by element (0 elements in either difference, sha256 equal).

| m | fastchain log (this folder) | candidates | survivors (ref = fast) | fastchain worst ratio (72-pt B4) | refchain worst ratio (own, every survivor screened) | set match | status |
|---|---|---|---|---|---|---|---|
| 112 | `fc_gap_112-124.log` | 5,317 | 5,299 | 0.000996 | earlier referee run (m=102-121), not re-run | yes | CLOSED |
| 113 | `fc_gap_112-124.log` | 8,419 | 8,404 | 0.001578 | earlier referee run, not re-run | yes | CLOSED |
| 115 | `fc_gap_112-124.log` | 21,105 | 21,097 | 0.003964 | earlier referee run, not re-run | yes | CLOSED |
| 122 | `fc_gap_112-124.log`; ref `refshapes_122.log` | 529,362 | 529,353 | 0.099607 | 0.0996069 | yes | CLOSED, 2 codes |
| 123 | `fc_gap_112-124.log`; ref `refshapes_123.log` | 838,840 | 838,829 | 0.157873 | 0.1578732 | yes | CLOSED, 2 codes |
| 124 | `fc_gap_112-124.log`; ref `refshapes_124.log` | 1,329,423 | 1,329,411 | 0.250223 | 0.2502232 | yes | CLOSED, 2 codes |
| 125 | `fc_gap_125-126.log`; ref `refshapes_125.log` | 2,106,794 | 2,106,776 | 0.396594 | 0.3965945 | yes | CLOSED, 2 codes |
| 126 | `fc_gap_125-126.log`; ref `refshapes_126.log` | 3,338,831 | 3,338,817 | 0.628587 | 0.6285874 | yes | CLOSED, 2 codes |
| 127 | `../target11_referee/chain127_refB4only.log` (earlier) | 5,291,301 | 5,291,294 | 0.996288 (earlier) | 0.9962878 (`refshapes_127.log`, earlier) | **yes (new)** | CLOSED, 2 codes |

* At every m the worst shape is K = 27,444,133,206,411,171,953, in both codes. fastchain: 0 failures,
  exact-needed 0, and "worst valid as global max: True". The refchain screen with B4 leaves 0 shapes open at every
  m, and the exact own chain gives 0 failures.
* fastchain and refchain agree to the 6-7 digits printed. They use different B4 grids (fastchain the 72 doubly
  computed points, refchain the 117-point snapshot).
* Compared with the earlier records: m = 126 gives 0.628587 here against 0.628592 (`chain_126_final.out`, full
  grid). m = 125 gives 0.396594 here against 0.636058 (`chain_757.out`, B4 to 757). Candidate counts are identical.
* Shapes the referee screen leaves open with B2+B3 only (they need B4), all closed with B4: 1 at m = 122 and 123,
  3 at 124, 4 at 125, 6 at 126.
* sha256 of the survivor lists (in increasing K, `"K p\n"` lines) are in the setcmp logs, for example
  m = 127: `544c846c1058da6aee302d3242ceca4fc907b2f1f09112545a4c35c469977771`.

## Remaining caveats

* At m = 112, 113 and 115 the B4 tables are not needed, but the doubly computed grid was used anyway. The
  referee's own chain was not re-run at these m in this batch. It was run earlier for m = 102..121.
* `setcmp`'s "FAST" side is `common.survives` with `lam_bound` cached per piece. The cache is safe because the
  NM tuple is equal at both ends of the piece and NM is monotone. The candidate enumeration itself is still
  fastshapes' alone. Its completeness rests on the referee's independent per-piece floor-sum count, which matched
  at every m.

## CPU

About 59 minutes of one core in all: batch 1 (fastchain) 32 min, batch 2 (refshapes 122-126 + setcmp) 21 min,
batch 3 (setcmp 113, 115, 127) 6 min. Peak commit 0.75 GB.
