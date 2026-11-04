# Shape completeness for "no m-cycle for m <= 127": an independent proof

Verdict: **PROVED, with one correction to the implementation's justification** (section 4, F1). The pruning
conditions are all necessary conditions. One step in the candidate enumerator (`fastshapes.box_points`, the
y-window built from midpoints with `pad = 2`) is **not** valid as written for every piece. For m = 111..127 it
fails only on pieces that contain no lattice point of the strip at all, by the best-approximation property of
continued fractions. So no shape is lost, but the reason is not the one the code relies on. A second finding is
about records, not mathematics (F3): this release has no chain log for m = 111, 112, 113, 115, 122, 123, 124.

## Clean-room note (what I read, and when)

Sessions on 2026-11-03 (Eastern time), in this order:

1. `METHOD.md`, all of it. It is short and its proof text for sections 1-4 covers results already proved
   independently. Section 5 is the only part about shapes, and it gives statements with no proof.
2. METHOD section 5 was too vague to say what is enumerated. It does not give the lower bound X used for the
   elements, how `v, tau` become integers `N, M`, which `m2` are tried, the `delta` and `ln 2` enclosures, or
   what the strip enumerator does. So I used the exception in my brief and read the enumeration code. **Deviation
   from the brief:** I read `computed/target7b_push/fastshapes.py` **in full** (190 lines). Its conditions and its
   arithmetic are interleaved, so I could not take the docstrings and conditions alone. In
   `computed/target1a/chain/` I read the docstring and the constants of `common.py`, and the functions `G`, `NM`,
   `tail`, `lam_bound`, `survives` and `Ub_cert`. I also read the docstring of `shapes.py` and its `convergents`,
   `rhin_ceiling` and `surviving`. I did not read `shapes.strip_points`.
3. The Lean *statements* (not the proofs) of `theorem21_two`, `windowExp`, `windowExp2`, `ratioIn_of_crude`,
   `RhinBound`, `numLocalMin` and `oddCount`, so that the hypotheses are quoted exactly.
4. I wrote sections 1-3 below. Before writing them I ran two quick checks of my own (scratchpad, each under 1
   minute): `padcheck.py` and `ycheck.py`. They led to finding F1.
5. Only after that did I read `computed/target7c_proofs/PROOFS.md` section 3 for the comparison in section 5. I
   have not read `collatz-loop/research/target10_rrise/WRITEUP.md`.

The two earlier independent proofs, `THEOREM-R-independent-proof.md` and `LEMMA22-CHAIN-independent-proof.md`, are
cited and were not needed here: shape completeness does not depend on them.

## 1. Setting, hypotheses, and the enumerated set

`T(n) = n/2` for even n and `(3n+1)/2` for odd n; `delta = log2 3`. A *cycle* is a finite set `Z` of positive
integers with `T(Z) = Z` on which T acts as a single cycle, of minimal period `p = |Z|`. It is *nontrivial* if
`Z != {1, 2}`. Its *local minima* are the odd `n in Z` whose predecessor in the cycle is even; `m` counts them.
`K` is the number of odd elements and `Lambda = p ln 2 - K ln 3`. An *m-cycle* is a nontrivial cycle with exactly
m local minima. (In Lean, `numLocalMin x p` and `oddCount T x p` with `p` the minimal period are these m and K.)

**Hypotheses** (not proved here):

* **H1 (Barina, `hX`).** Every `0 < n <= 2^71` reaches 1 under the Collatz map `C` (`C(n) = n/2` or `3n+1`).
* **H2 (Rhin via Simons-de Weger Lemma 12, `RhinBound`).** For every nontrivial positive cycle with `K >= 1`:
  `Lambda > exp(-13.3 (0.46057 + ln K))`.

**Results used, proved in Lean (statements quoted):**

* **L1 (`theorem21_two`).** If every element of the cycle is `>= X0 > 0` (X0 real) and `1 <= m2 <= m`, then
  `Lambda < (m - m2)/X0 + 1/(2^v - 1) + (m2 - 1)/(2^tau - 1)`, where `v = m2 K / (m G(m2))`,
  `tau = m2 K / (m (1 + G(m2 - 1)))` and `G(j) = sum_{d<j} delta^d` (real exponents). Both sides of the Lean
  statement carry a factor 3, which cancels.
* **L2 (Remark 7; the bound behind `ratioIn_of_crude`).** Under the same lower bound: `Lambda < m/X0`.

**Trusted arithmetic.** The code takes `DLO < delta < DHI` (width < `10^-110`) and `L2LO < ln 2` from
mpmath interval arithmetic at 110 digits. `DU = 1.58496250072116 > DHI` is asserted in code. The Rhin-ceiling
test `g_ok` uses mpmath `iv`. I treat mpmath's interval arithmetic as correct.

**The enumerated objects** (for each m; the definitions are the code's, restated):

* `G_U(j) = sum_{d<j} DU^d` (an exact rational), `NCAP = 400`, `X0 = 2^71 + 1`.
* `NM(m, m2, K) = (N, M)` with `N = min(floor(m2 K / (m G_U(m2))), 400)` and
  `M = min(floor(m2 K / (m (1 + G_U(m2 - 1)))), 400)`. It is undefined when `N < 1` or `M < 1`.
* `lam_bound(m, K) = min( m/X0, min over m2 in [1, m] with NM defined of (m - m2)/X0 + 1/(2^N - 1) + (m2 - 1)/(2^M - 1) )`.
* `survives(m, K, p)` holds iff `p > K DLO` and `p - K DHI < lam_bound(m, K)/L2LO`.
* `Kceil(m)`: an integer `>= kmono = ceil(2 * 13.3 G_U(m)/L2LO)` at which the interval lower bound of
  `g(K) = (K/G_U(m) - 2) ln 2 - ln m - 13.3 (0.46057 + ln K)` is `>= 0`. The code finds it by bisection on
  `[kmono, 10^40]`.
* `Surv(m) = {(K, p) : 1 <= K < Kceil(m), survives(m, K, p)}`. These are the *survivors* (5,291,294 at m = 127).
* `Cand(m)`: the union over the merged pieces `[Ka, Kb)` of `fastshapes.box_points(Ka, Kb, eta)`, restricted to
  `1 <= K < Kceil`. These are the *candidates* (5,291,301 at m = 127). `fastchain.candidates` builds exactly this
  set, and the chain is run over it.

## 2. The theorem

**Theorem S.** Assume H1 and H2. If an m-cycle exists, then its pair `(K, p)` lies in `Surv(m)`. If, in addition,
the finite check C1 below holds for this m, then `(K, p)` lies in `Cand(m)`. C1 was run and holds for every
m = 111..127. The argument does not use `m <= 127` anywhere else, so it holds for every m.

The rest of this section proves the first statement (Lemmas A-E). Section 3 proves the second (Lemma F).

**Lemma A (elements exceed 2^71).** Every element of a nontrivial cycle is `>= 2^71 + 1`.
*Proof.* Take n in Z. For odd n, `T(n) = C(C(n))`. For even n, `T(n) = C(n)`. So the T-orbit of n is a
subsequence of its C-orbit, and the only C-values the T-orbit skips are `3k+1` for odd k, which are even and `>= 4`.
If the C-orbit reached 1, then 1 would lie on the T-orbit, so `1 in Z` and hence `Z = {1, 2}`, a contradiction.
So n does not reach 1, and by H1 `n > 2^71`. []

So L1 and L2 apply with `X0 = 2^71 + 1`. The code's `X0` is exactly this value.

**Lemma B (K >= 1, Lambda > 0).** *Proof.* If every element were even, T would halve each one, and the cycle
would strictly decrease. So `K >= 1`. Multiplying `T(n)/n` over the cycle gives 1. Each even element contributes
`1/2`, and each odd element contributes `(3/2)(1 + 1/(3n))`. So `2^p / 3^K = prod_{odd n} (1 + 1/(3n)) > 1`, which
gives `Lambda > 0`. []

Since `delta` is irrational, Lemma B gives `p > K delta`. L2 with Lemma A gives
`0 < p - K delta < m/(X0 ln 2) < 1` for `m < 1.6 * 10^21`, so `p = ceil(K delta)`. The enumerator does not use this
fact; it is a consequence only.

**Lemma C (every pruning bound is a valid upper bound on Lambda).** For the cycle, `Lambda < lam_bound(m, K)`.
*Proof.* The `m/X0` term is L2. Take any `m2` in `[1, m]` with `NM(m, m2, K) = (N, M)` defined. Because
`0 < delta < DU`, we have `G_U(m2) >= G(m2)` and `1 + G_U(m2 - 1) >= 1 + G(m2 - 1)`, so `N <= m2 K/(m G(m2)) = v`
and `M <= tau`. Capping at 400 only lowers N and M. Since `N >= 1`, `0 < 2^N - 1 <= 2^v - 1` and so
`1/(2^N - 1) >= 1/(2^v - 1)`. Likewise `(m2 - 1)/(2^M - 1) >= (m2 - 1)/(2^tau - 1)`, using `m2 - 1 >= 0` and
`M >= 1`. So each Theorem-21 term in `lam_bound` is at least the right side of L1, which is greater than `Lambda`.
Any m2 that is skipped only makes the minimum larger, and that is safe. []

**Lemma D (the cycle survives).** `survives(m, K, p)` holds.
*Proof.* `p > K delta > K DLO`. Since `DHI > delta`, `p - K DHI < p - K delta = Lambda/ln 2`. Lemma C gives
`Lambda/ln 2 < lam_bound/ln 2`, and since `lam_bound > 0` and `ln 2 > L2LO`, `lam_bound/ln 2 < lam_bound/L2LO`.
Both pruning tests in `survives` are therefore implied by the cycle's existence; they never reject a true shape.
(For K up to `10^40` the enclosure cannot misjudge the sign of `p - K delta`. Since `|p - K delta| > 1/(2 q)` for
the next convergent denominator `q`, it is far larger than `K (DHI - DLO) < 10^-70`. This is not needed for the
direction of the proof.) []

**Lemma E (Rhin ceiling).** `K < Kceil(m)`.
*Proof.* Suppose `K >= Kceil`. Put `v' = K/G_U(m) <= K/G(m) = v`, where v is L1's exponent at `m2 = m`. At
`m2 = m`, `tau >= v`: the difference of the denominators is `G(m) - 1 - G(m - 1) = delta^(m-1) - 1 >= 0`. So L1
with `m2 = m` gives `Lambda < 1/(2^v - 1) + (m - 1)/(2^tau - 1) <= m/(2^v' - 1)`. Here
`K >= kmono > 26 G_U(m)`, so `v' > 1`, `2^v' - 1 >= 2^(v'-1)`, and therefore `Lambda < m 2^(1 - v') < m 2^(2 - v')`.
That is, `ln Lambda < ln m + (2 - v') ln 2 = -g(K) - 13.3 (0.46057 + ln K)`.

Now the monotonicity. For `K > 13.3 G_U(m)/ln 2`, `g'(K) = ln 2/G_U(m) - 13.3/K > 0`. We have
`kmono = ceil(26.6 G_U(m)/L2LO) > 13.3 G_U(m)/ln 2`. Bisection only ever lowers `hi` from `10^40` to midpoints
above `lo >= kmono`, so `Kceil > kmono`, and `g_ok(Kceil)` certifies `g(Kceil) >= 0`. Then g is increasing on
`[Kceil, infinity)`, so `g(K) >= 0` and `ln Lambda < -13.3 (0.46057 + ln K)`. This contradicts H2, whose
hypotheses (nontrivial, so no element is 1 or 2, and `K >= 1`) hold. Bisection need not find the least such K;
any certified `Kceil >= kmono` is valid. []

Lemmas D and E together put `(K, p)` in `Surv(m)`. This proves the first statement of Theorem S. []

## 3. The enumerator outputs a superset of Surv(m)

**Lemma F.** `Surv(m) ⊆ Cand(m)`, given check C1.

Fix a true shape `(K, p)`. By Lemmas C and D it satisfies `0 < p - K delta < lam_bound(m, K)/ln 2`. All that is
needed is that the box enumerator returns every lattice point with `1 <= K < Kceil` and
`K DLO < p < K DHI + lam_bound(K)/L2LO`. (Points of `Surv` satisfy these conditions by definition, so the proof
covers all of `Surv`, not just true shapes.)

**F.1 Pieces and their bound L.** `thresholds` lists, for every `m2 in [1, m]` and `j in [1, 400]`, the least K at
which `floor(m2 K/(m G_U(m2))) >= j`, namely `ceil(j m G_U(m2)/m2)`, in exact rationals. It does the same for M.
So on each interval between consecutive events, the running counters `N[m2]`, `M[m2]` equal `NM(m, m2, K)`
exactly, and `cur` is the float value of `lam_bound` there. The pieces start at `Ka = 1`, are contiguous, and end
at `Kceil`.

*Float safety (this is the G2 point, made rigorous).* Each term of `cur` comes from at most three IEEE
operations on exact or conservatively rounded inputs:

* `float(2^71 + 1) = 2^71 < X0`, which errs in the safe direction.
* `2.0**N` is exact for `N <= 400`.
* `2.0**N - 1`, the divisions, and the sum of three positive terms each have relative error at most `2^-53`.

So the computed `cur` is at least `lam_bound * (1 - 8 * 2^-53)`. The code multiplies it by `1 + 10^-9`, which
gives `L >= lam_bound` on the piece. `merge` replaces each run of pieces by its first L. That is valid because
`lam_bound` is non-increasing in K: each N and M only steps up, so each term only falls. The float `cur` follows
the same monotone sequence, and checking the merged list directly found no increase at m = 111 or m = 127.
Finally, `eta = F(L)/L2LO * (1 + 10^-9) >= lam_bound/L2LO`, exactly.

**F.2 The x-range is rigorous.** In `box_points`, let `pa = floor(Ka DLO)` and `e_a = pa - Ka delta`, which lies in
`[ea_lo, ea_hi]`. Set `K' = K - Ka`, `p' = p - pa` and `e' = p' - K' delta = e - e_a`. A true point has
`0 < e < eta`, so `e'` lies in `(elo, ehi)` with `elo = -ea_hi` and `ehi = eta + Kb (DHI - DLO) - ea_lo`.

Consecutive convergents `(q_n, p_n)`, `(q_{n+1}, p_{n+1})` of delta form a basis of Z^2 with determinant
`s = +-1`. They really are convergents: every partial quotient was certified from both ends of the enclosure, and
I re-checked `|s| = 1` for all 79 consecutive pairs. Writing `(K', p') = x (q_n, p_n) + y (q_{n+1}, p_{n+1})` and
`e_j = p_j - q_j delta` gives `x = s (K' e_{n+1} - e' q_{n+1})`. This is affine in each of `K' in [0, Lk]`,
`e' in [elo, ehi]` and `e_{n+1} in EJ[n+1]` separately, so its extremes over the box are at the 8 vertices.
Those vertices are exactly what the code evaluates, with an extra margin of +-1. So every true point's x is
enumerated. The y bounds `ka`, `kb` from `0 <= K' < Lk` are also exact (integer floor division, widened by 1).

**F.3 The y-window from e' is NOT rigorous as written (finding F1).** For each x the code bounds y by
`(e' - x e_n_mid)/e_{n+1}_mid` at the midpoints of the enclosures of `e_n` and `e_{n+1}`, widened by `pad = 2`. The
rigorous range is the extreme of `(e' - x e_n)/e_{n+1}` over the interval vertices; it is monotone in each
variable separately because the sign of `e_{n+1}` is fixed. The midpoint error is about
`|x| q_n (DHI - DLO) / |e_{n+1}|`. It is negligible when the chosen basis is moderate, but not when the piece's
`eta` is so small (around `10^-119`, the regime where N reaches its cap of 400) that the cost heuristic picks the
last convergents available (`q ~ 5 * 10^37`). Then `|x| ~ 10^37` and the error reaches hundreds.

**Check C1** (`ycheck.py`, scratchpad, exact rationals). For every merged piece and every x the code iterates
over, it compares the rigorous y-range with the code's `[ya, yb]`. Whenever the rigorous range is not inside, it
tests whether the piece is *empty*. By the best-approximation property, `|K delta - p| >= |e_j|` for all
`1 <= K < q_{j+1}` and all integers p. So if `q_j <= Kb < q_{j+1}` and `eta < min |EJ[j]|`, the piece contains no
point with `0 < p - K delta < eta`. Results:

| m | pieces | x iterations | rigorous range not inside code window | of which provably empty | uncovered |
|---|---|---|---|---|---|
| 111 | 955 | 4,619 | 4 | 4 | 0 |
| 112, 113, 115, 116, 118, 119, 120, 121, 123, 124, 127 | - | - | 0 | - | 0 |
| 114 | 3,626 | 17,654 | 4 | 4 | 0 |
| 117 | 7,144 | 38,003 | 4 | 4 | 0 |
| 122 | 12,207 | 96,337 | 4 | 4 | 0 |
| 125 | 15,051 | 173,366 | 4 | 4 | 0 |
| 126 | 15,983 | 211,044 | 5 | 5 | 0 |

At m = 127: 16,912 pieces and 258,806 x iterations. The smallest margin of the code window over the rigorous range
is 2.000002, so the window contains it everywhere. All the failures are in the last pieces (`Ka ~ 10^25` up to
`Kceil`, `eta < 10^-118`), which contain no strip point at all. For every m = 111..127 the uncovered count is
zero. So `Surv(m) ⊆ Cand(m)`. []

C1 runs in 1-41 s per m. The scripts are not part of the release; they were run from the session scratchpad:
`C:\Users\HACKAT~1\AppData\Local\Temp\claude\C--Users-hackathon-Documents-GitHub-collatz-loop\2e4be3f3-dd60-48d4-8490-2a1b9ab6b2e2\scratchpad\ycheck.py`
and `padcheck.py` beside it. Run them from `computed/target1a/chain` with `MPMATH_NOGMPY=1`. It reuses the code's own piece construction and basis choice, but tests each window
against exact interval vertices.

## 4. Hypotheses and status, in one place

* **External:** H1 (Barina, every `n <= 2^71` reaches 1) and H2 (`RhinBound`). These are used in Lemma A and
  Lemma E, and nowhere else.
* **Lean-proved, cited:** L1 (`theorem21_two`) and L2 (Remark 7).
* **Trusted numerics:** mpmath interval enclosures of `delta`, `ln 2` and `g(K)`; IEEE double semantics (F.1).
* **Not used:** Theorem R, Lemma 2.2, the chain theorem, and the B_r tables. Shape completeness is independent of
  them.
* **Not needed by the enumerator:** `p = ceil(K delta)`, and the "Remark-7 strip". The strip is implied (Lemma C
  includes `m/X0`) but is not a separate step in `fastshapes`.

**Findings.**

* **F1 (corrected justification).** `box_points`' midpoint-plus-pad y-window is not a sound containment in
  general. At m = 111, 114, 117, 122, 125 and 126 it misses part of the rigorous range in 4-5 pieces each. Every
  such piece is empty by best approximation, so no candidate is lost (C1). Suggested fix: compute ya and yb from
  the interval vertices, as is already done for x, or skip pieces whose eta is below the best-approximation floor.
* **F2 (G2, closed).** The float bound L is rigorous by the error count in F.1. The `1e-6` slack in `merge`'s
  assert is never exercised, because L is monotone.
* **F3 (records, not mathematics).** Completeness is per m. The chain must be run over `Cand(m)` for every
  m = 111..127. In the release I found closing logs for m = 114 and 116-121 (`target7b_push/final_runs.out`) and
  for m = 126 and 127 (`target11_fourrise/chain_12{6,7}_final.out`). The development repository adds m = 125
  (`research/target11_fourrise/chain_757.out`, B4 to 757). I found **no log for m = 111, 112, 113, 115, 122, 123
  or 124.** Nothing guarantees that closing a larger m implies closing a smaller m (the candidate sets differ), so
  these runs either need to be found or redone.
* **Nothing false.** No pruning step rejects a shape that a cycle could have.

## 5. Comparison with PROOFS.md section 3 (read after sections 1-4 were written)

PROOFS.md section 3, "Shape completeness", items 1-5, compared with sections 1-4 above:

| PROOFS section 3 | This proof | Assessment |
|---|---|---|
| E1: elements `>= 2^71 + 1` (stated) | Lemma A: proves it from H1, which is stated for C, via the T/C orbit relation | Small gap in PROOFS (step not written); true |
| "Λ > 0 for a cycle" (asserted) | Lemma B: product identity | Small gap in PROOFS; true |
| Item 1: strip, `p = ceil(K delta)` | Same, but the enumerator does not need it | Agree |
| Item 2: `Λ < m 2^(2 - K/G)`, g increasing, bisection "rigorous" | Lemma E: makes `tau >= v` (`delta^(m-1) - 1 >= 0`), `v' <= v` and `v' > 1` explicit; any certified `Kceil >= kmono` is valid | Agree; PROOFS gives only a sketch |
| Item 2 note: DU only shrinks N | Lemma C: N <= v and M <= tau, the cap, and skipped m2 | Agree |
| E2 / G1: cite `theorem21_two`, not `lambda_lt_two` | Cites `theorem21_two` directly | Agree |
| Item 3: `survives` is conservative | Lemma D | Agree |
| Item 4 / G2: float L safe, merge monotone | F.1: explicit IEEE error count, and a check that the float L never increases | Agree; G2 is closed |
| Item 4: "box bounds (x from corners, **y with pad 2**, K' range) are correct supersets" | F.2 agrees for x and K'. **F.3 / F1: the y-window with pad 2 is not a superset in general.** It fails on 4-5 pieces at m = 111, 114, 117 (inside PROOFS' range m <= 121), 122, 125 and 126. | **PROOFS item 4 is wrong as stated.** It is harmless because every failing piece is provably empty (C1) |
| Item 5: independent enumeration at m = 104, 110 | Not repeated. C1 checks fastshapes' own pieces at every m = 111..127 | Complementary |
| No mention of per-m run coverage | F3: no chain logs for m = 111, 112, 113, 115, 122, 123, 124 | Gap in the record |

**Do the code's conditions match the proved necessary conditions?** Yes, condition by condition:

* `X0 = 2^71 + 1` is Lemma A.
* `p <= K DLO` rejects, which is Lemma B.
* `NM` with `G_U` and the 400 cap is Lemma C.
* `lam_bound` includes the m/X0 term, which is L2.
* The `survives` inequality is Lemma D.
* `rhin_ceiling` (kmono, bisection, `g_ok`) is Lemma E.
* `fastchain.candidates` restricts to `1 <= K < Kceil` (Lemmas B and E) and adds no other pruning.

No code condition is stronger than a proved necessary condition. The one place where the code's *enumeration*
(as opposed to its *pruning*) is not justified by its own construction is the y-window, F1. The candidate set
still contains every survivor, by C1.

**One written proof or one implementation?**

* *Written proofs.* Shape completeness now has two written proofs: PROOFS section 3, a sketch with the item-4
  error noted above, and this note. With Theorem R, Lemma 2.2, Corollary 2.3 and the chain theorem already done
  twice, I know of no theory step of the m <= 127 argument that still has only one written proof.
* *Implementations.* Each step has two implementations except:
  * **The survivor/candidate sets at m = 122..126.** These come from `fastshapes` alone. The independent
    enumerations are Referee 1 at m = 102..121, `enum7c` at m = 104 and 110, and `refshapes` (a floor-sum count)
    at m = 127. C1 checks fastshapes at these m but uses its own piece construction, so it is not an independent
    enumeration.
  * **The four-rise chain run over all candidates at m = 122..126.** This is `fastchain` alone. At m = 127 the
    referee's `refshapes` part (B) screened every survivor with its own chain, and `sample50` ran its own chain on
    51 shapes.
  * The missing-log values of m in F3, where I could not confirm that even one run exists in the record.
