# Target 13: past m = 127

Labels: [proved] chain theorem (METHOD.md §4) applied to exact tables; [computed] exact computation;
[heuristic] model or synthetic grid values. Nothing here is committed, published or in Lean.

## 1. Why m = 128 fails (scoping) [computed: exact chain, real grids]

`trace.py 128`: the hard shape K = 27,444,133,206,411,171,953 (worst shape for every m >= 110) runs through phases:

| steps t | rule | Y range | grid used |
|---|---|---|---|
| 1..24 | 4-windows (a few 2/3 at the start) | 72 -> 1,328 | B4 to 852 |
| 25..48 | 3-windows | 1,328 -> 56,689 | B3 to 38,243 |
| 49..62 | 2-windows (two delta steps at the 3->2 hand-over) | 56,689 -> 1.59e6 | B2 to 1,039,710 |
| 63..m-1 | pure delta steps (Lemma 20) | 1.6e6 -> ~1e19 | none |

Each extra m appends one delta step, so the ratio is multiplied by about 1.585 (0.9963 -> 1.579). The ratio 0.99629
is the same at m = 121 and 127 because both chains leave the grids through the same top B2 point. To gain one m
the slow phase must last one step longer, which means *extending a grid past its top*. Tightening binding values
below the tops does not help: filling every gap of the B4 grid below 852 changes the ratio from 0.9963 to 0.9962.

## 2. Routes ranked [heuristic: synthetic B = N + gap model, b = +6 pessimistic; chain itself exact]

`explore.py`, single-point tests. One new point beyond a top gives about +1 m:

| new point(s) | m reached (hard shape) | CPU-h per point (central, range) | memory |
|---|---|---|---|
| B2 at ~1,600,000 | 128 (0.9975) | measured below | < 0.5 GB |
| + B2 at ~2,540,000 | 129 (0.9988) | ~2.5-5 | < 0.5 GB |
| + B3 at ~56,800 | 130 (0.9982) | ~2 (1.5-3.5) | ~1-2 GB |
| + B2 at ~4,015,000 | 131 | ~5-12 | < 1 GB |
| B5 to 72 / 150 (new code) | +1 (b = 0; +0 at b = +6) / +2 | few CPU-h, plus new code and referee | ~1-4 GB |
| B4 to 1,400 | +1 | ~50-100 | ~2 GB |
| denser B4/B3 below their tops, LP over windows | ~0 | - | - |

B2 tolerates huge errors (gap +30 still closes); B3 at 56,800 tolerates b = +12.

## 3. Generalisation [heuristic, checked against the exact chain]

    m* ~= 1 + L_1 + sum_{r=2..R} L_r,   L_r = log_delta(T_r / x0),   L_1 = log_delta(K_h (delta-1)/delta / x0)

T_r = top of the B_r grid (dense enough from x0 up), x0 = log2 Ub of the hard shape (~ K_B + 0.85 for Barina's
2^K_B), K_h = hard-shape K (heuristically ~ 1.5 * 2^K_B / m). Derivation: in phase r the chain grows by delta per
r steps; the last (delta) phase ends where Y delta/(delta-1) ~ K; telescoping. `formula.py`: on 12 grid scenarios
the continuous m (m + log_delta(1/ratio)) is within -0.7..+0.9 of the rule; real grids: rule 126.5, chain 127.0.

* +1.505 m per doubling of any one level's top; ~+1.4 m per extra verified bit (discrete in practice: K_h is a
  convergent denominator).
* With B_r cost ~ N^{e_r}, level r gives 1.505 max(0, log2 W / e_r - log2 x0): m grows only logarithmically in
  compute, and levels beyond r ~ 1 + log2 W / (2 log2 K_B) (6-7 for W ~ 1e12 operations) add nothing.
* What is proved: only the chain theorem for given exact tables. The rule is a model of where the computation lands.
* A proved B_r(N) <= N + O(r log N) for all N would remove the delta phase; that is an open digit-run problem for
  1/3^k (target10 WRITEUP 2.3).

## 4. Shape enumeration fix (referee F1)

`shapes13.py`: `box_points` with the y-window computed from the corners of the enclosures of e_n, e_{n+1} (exact
Fractions, +-1 pad) instead of midpoints +-2. Monkey-patched into fastshapes by `fastchain13.py`.

## 5. Runs and CPU ledger

| run | lease | CPU | result |
|---|---|---|---|
| shapes y-window fix vs original, m = 110/115/120 | local 1 thr | 40 s | identical sets (2130 / 21105 / 210755) — `cmp_shapes.log` |
| B2(1,600,000) b2fast | local 1 thr | 2123 s | **1,600,019** (gap 19) |
| B2(1,600,000) referee myb2 | Modal 4 cpu | 754 s wall | **1,600,019** — agrees |
| chain m = 128, all shapes (fixed enumerator, +B2(1.6e6)) | local 1 thr | 2050 s | 8,385,563 candidates, 0 failures, worst 0.997472 at the hard shape — **CLOSED** (`chain_128.out`) |
| B2(56,800) b2fast | local | 4 s | 56,813 (Kmax for B3) |
| B2(2,540,000) b2fast | local 1 thr | 6062 s | **2,540,021** (gap 21) |
| B2(2,540,000) referee myb2 (all hits >= N+16) | Modal 4 cpu | 1869 s wall | **2,540,021** — agrees |
| chain m = 129, all shapes | local 1 thr | 3089 s | 13,289,304 candidates, 0 failures, worst 0.998809 (hard shape) — **CLOSED** (`chain_129.out`) |
| B3(56,800) b3join (t = 24) | local 1 thr | 3275 s, 3.3 GB peak | **56,828** (gap 28), witness ks (47273, 4149, 5406) |
| B3(56,800) referee myb3 (all hits >= N+27, KQ = 56,813) | Modal 4 cpu | 11,470 s wall | **56,828** — agrees |
| B2(56,800) referee myb2 | local 1 thr | 3 s | 56,813 — agrees (the Kmax used by both B3 codes) |
| chain m = 130, all shapes | local 1 thr | 5225 s | 21,060,865 candidates, 0 failures, worst 0.998225 (hard shape) — **CLOSED** (`chain_130.out`) |
| B2(4,015,000) referee myb2 (all hits >= N+16) | Modal 4 cpu | 4290 s wall | **4,015,020** |
| B2(4,015,000) b2fast | Modal 1 cpu | 24,457 s (Modal core ~4x slower than local) | **4,015,020** — agrees with myb2 (same maximiser k0 = 1,085,023, l0 = 1) |
| chain m = 131, all shapes | local 1 thr | 6844 s | 33,377,017 candidates, 0 failures, worst 0.998291 (hard shape) — **CLOSED** (`chain_131.out`) |

Totals: local ~28,700 CPU-s = **8.0 CPU-h** (1 thread throughout, peak commit 3.3 GB); Modal ~99,200 core-s =
**27.6 core-h, $1.71** (billing report; ledger in collatz-loop/personal/modal-ledger.md). All Modal logs are in
`modal_logs/`, each with the sha256 manifest of the code it ran (identical to main at 315e822).

## 6. Result [computed; same status as m <= 127: exact, doubly computed tables, not in Lean]

**No m-cycle for m <= 131** (given Barina 2^71 and Rhin), extending m <= 127 by four new table points, each computed
by two independent codes with identical values:

| point | value | code 1 | code 2 |
|---|---|---|---|
| B2(1,600,000) | 1,600,019 | b2fast (local) | myb2 (Modal) |
| B2(2,540,000) | 2,540,021 | b2fast (local) | myb2 (Modal) |
| B2(4,015,000) | 4,015,020 | b2fast (Modal) | myb2 (Modal) |
| B3(56,800) | 56,828 | b3join (local) | myb3 (Modal); Kmax B2(56,800) = 56,813 by b2fast and myb2 |

Spot rule: the 1.6e6 and 2.54e6 points were computed locally and on Modal (different codes) with identical results.

| m | candidates (fixed enumerator) | failures | worst ratio (hard shape K = 27,444,133,206,411,171,953) |
|---|---|---|---|
| 128 | 8,385,563 | 0 | 0.997472 |
| 129 | 13,289,304 | 0 | 0.998809 |
| 130 | 21,060,865 | 0 | 0.998225 |
| 131 | 33,377,017 | 0 | 0.998291 |

Caveats: the m >= 128 chains used one implementation (fastchain + chainr, as refereed for m <= 127) and the
patched enumerator; no independent chain (refchain) or independent survivor count has been run at m = 128..131.
That is the cheapest remaining double-check (refchain on the hard shapes: seconds; refshapes survivor count:
about 1-3 CPU-h per m, parallel on Modal). Margins are as thin as at 127 (0.1-0.25%), but B2 tolerates +30 on
its new points and B3(56,800) about +12 (heuristic tolerance tests, section 2).

The phase-sum rule held: each new point past a grid top gave exactly +1 m, as predicted.

## 7. What each further m costs [heuristic: synthetic lookups; costs extrapolated from the measured runs]

| m | cheapest new point(s) (hard shape lookups) | main CPU | referee | all-shapes chain (1 thread) |
|---|---|---|---|---|
| 132 | B3 at ~90,000 (or B2 at ~6.35e6, or B4 at ~1,330, or B5 at 72 with new code) | B3: ~3 h (b3join ~N^2.5) | myb3 ~10-40 core-h (depends on V margin) | ~3 h (53M shapes) |
| 133 | + B2 at ~6.35e6 | ~13 h local (b2fast ~N^2.3), ~50 h on a Modal core | myb2 ~12 core-h | ~5 h |
| 134 | + B3 at ~142,500 (or B2 at ~9.5e6) | B3 ~9 h; B2 ~33 h | ~40-150 / ~30 core-h | ~7.5 h |
| 135 | + the other | | | ~12 h |

Each +1 m along one axis costs about delta^e times the previous point on that axis (e ~ 2.3 for B2, ~2.5 for B3:
x2.9-3.2 per m), and the shape count grows x1.585 per m, so the chain alone reaches ~12 h at m = 135. Alternating
B2/B3 points keeps the per-m cost to roughly x1.7-2. The rule predicts the m; it gets expensive around m ~ 134-136.
Next cheap axis not yet used: B5 at small N (new join code + validation + referee; +1 to +2 m).

## 8. Independent check of m = 128..131 (referee code) [computed]

`ref13.py` drives the referee's own code unmodified (`target11_referee/refchain.py`, `refshapes.main_stream`,
`target11_gapfill/setcmp.py`); the only injections are this folder's four doubly computed points into
`refchain.load_grids` and the endpoint y-window into the candidate stream. refchain uses the 117-point B4 snapshot
(fastchain used the run11 B4 grid), so the two chains share no chain code and no B4 table file.

* refchain on the hard shapes (`refchain_hard_128-131.log`, all four new points loaded): hard shape 0.2507265 /
  0.3973921 / 0.6298516 / **0.9982912** at m = 128..131 (fastchain at 131: 0.998291; at 128-130 fastchain had
  fewer of the new points, hence its larger ratios). Next worst K = 205,632,218,873,398,596,256: 0.7926643 at 131.
* refshapes (`refshapes_128..131.log`): own Rhin check passes, own floor-sum survivor count equals the count of
  candidates passing its own exact test in every piece (0 mismatches, 0 ambiguous) -> candidate list contains all
  survivors; own screen of every survivor with B4: 0 open; own exact chain on the open/top-50 shapes: 0 failures.
* setcmp (`setcmp_128-131.log`): referee survivor set == common.survives set (fastchain's test), element by element:

| m | candidates | survivors | sha256 of survivor list (`"K p\n"`, increasing K) |
|---|---|---|---|
| 128 | 8,385,563 | 8,385,549 | 83b95cec3934193ca41180599e064b76ae0c9ccc5b2ad6b1f124a3f3bc6ba5a2 |
| 129 | 13,289,304 | 13,289,292 | 153ef11f501809b9b78acc9d65e486db816c6c74aa22b068a0fe5374797893ee |
| 130 | 21,060,865 | 21,060,852 | 4ce9aeaf8e41eb6bf7c239ae9f2d991e5adad6325b9bf0d655e109fd2961625e |
| 131 | 33,377,017 | 33,377,004 | 7225b86738968feefde69f4cf1e3062746065a00d52bf5a7ced53c1f8c177870 |

Cost: one local thread, ~70 min, peak commit 0.2 GB (lease `collatz-m128-4495`). **Status of m <= 131: closed by
two independent chain implementations on doubly computed tables, survivor sets identical** (still not in Lean;
same external hypotheses).

## 9. m = 132 [computed; two codes for the new point, two chain implementations]

| run | where | CPU | result |
|---|---|---|---|
| B3(90,000) b3join, first try (s = 8, 256 partitions) | local 1 thr | 466 s, killed | projected 6.5 h > ETA: every partition re-enumerates Q (`b3_90000_s8_killed.log`) |
| B3(90,000) b3join via `b3drive.py 90000 6` (64 partitions; s is a performance parameter only) | local 1 thr | 15,388 s, 5.2 GB peak | **90,031** (gap 31), witness ks (44137, 23465, 22429). One partition (j = 21, key prefix 010101: the periodic 1/3 pattern) held 1.52e9 structured false matches and took 4,470 s |
| B2(90,000) (Kmax) | b2fast inside b3join; myb2 local | 6 s | 90,015 / 90,015 — agree |
| B3(90,000) referee myb3 (all hits >= N+28, KQ = 90,015) | Modal 8 cpu | 18,994 s wall, $2.84 | **90,031** — agrees, same maximiser (44137, 2, 23465, 4) |
| chain m = 132, all shapes | local 1 thr | 11,515 s | 52,895,924 candidates, 0 failures, worst **0.984008** (hard shape) — CLOSED (`chain_132.out`) |
| refchain hard shapes m = 132 | local | s | hard shape 0.9840082 (`refchain_hard_132.log`) |
| refshapes m = 132 | local 1 thr | ~800 s | floor-sum = own test in every piece; 52,895,906 survivors; screen with B4: 0 open; exact own chain 0 failures |
| setcmp m = 132 | local 1 thr | ~1,000 s | SETS IDENTICAL, sha256 5ca79c4a912f2f4555d8d625d7d80672138abe3a4e1d6f08f2465d5add4f30ff |

**m <= 132 closed**: five doubly computed new points (B2 at 1.6e6, 2.54e6, 4.015e6; B3 at 56,800, 90,000), two
chain implementations, identical survivor sets at every m = 128..132. Not in Lean; hypotheses Barina 2^71, Rhin.

Lesson for B3 beyond 65,000: b3join's packed path stops at N < 65,000; the unpacked path pays one Q enumeration
per partition and a fixed structured cluster in the 0101 partition (it grows ~N^3). myb3 (exhaustive small-K
branch) has no such cluster and on 8 cores was faster in wall time. For B3 at ~142,500 (m = 134) expect b3join
~15-25 h local (s = 6 or 7) and myb3 ~20-25 h wall on 8 Modal cores (~$10-12, i.e. over the $10 per-job limit
unless split across containers by partition).

## 10. m = 133 [computed; two codes per new point, two chain implementations]

One B2 point near the grid top does not close m = 133: a point a little above the looked-up N gains nothing over
the delta step. The gain has to come from filling the B2 grid where the hard shape looks. A cost-greedy search over
the 17 missing lookups gave 8 points (dropping any one pushes the hard shape above 0.995):

| N | B2 (b2fast, local) | myb2 (Modal) |
|---|---|---|
| 142591 | 142606 | 142606 |
| 227256 | 227273 | 227273 |
| 360191 | 360209 | 360209 |
| 579108 | 579125 | 579125 |
| 1478908 | 1478927 | 1478927 |
| 2344024 | 2344044 | 2344044 |
| 3715201 | 3715221 | 3715221 |
| 5888465 | 5888484 | 5888484 |

* b2fast: 1 local thread, sequential, preemptible lease `collatz-m128-4508`, ~16.6 h in total (5,888,465 alone 23,531 s), peak 1.1 GB.
  myb2: Modal 4 cpu each, $1.13.
* chain m = 133, all shapes (`chain_133.out`): 83,829,317 candidates, 0 failures, worst **0.923646** (hard shape), 14,957 s.
* refchain hard shape 0.9236464; refshapes: floor-sum = own test in every piece, 83,829,302 survivors, 0 open, 0 failures;
  setcmp: SETS IDENTICAL, sha256 366cf71609087eb66fc1a14414a7d3eb7ab3d3bad4bac8793de735f70eb4acf2.

**m <= 133 closed** (computed, not in Lean; Barina 2^71 and Rhin).
