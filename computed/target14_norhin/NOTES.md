# target14_norhin: removing `RhinBound` from the m <= 111 theorem

Lane D89. Branch `lean-no-rhin` (local only, never pushed). Status 2026-11-03: **step 1 (analysis) done,
no Lean changes yet.**

## How `RhinBound` enters

- Defined in `Collatz/HercherRhin.lean`. It is a hypothesis restricted to cycles:
  `exp(-13.3 (0.46057 + log K)) < p log 2 - K log 3`.
- It is consumed in exactly two places:
  - `K_lt_of_rhin` (m = 91), and
  - `K_lt_of_rhinOK` (`HercherAll.lean`, general m).
- Every m <= 111 file reaches it through `rhinOK m Kceil V cexp kexp`, inside `mOK_sound` (`MCycleWalk`) and
  `mOK3_sound` (`MCycleChain3`, `Chain3D`).
- Its only job is the ceiling `K < Kceil(m)`. Lemma 7 (`theorem21_vertexFree`, m2 = m) gives
  `Lambda < 2m 2^(-K/G_m)`. Against Rhin's lower bound this fails for `K >= Kceil`.
  - m = 111: `G_111 = 2.72e22`, `Kceil = 3.16e25`, `V = 1161`.
- Below `Kceil` the bootstrap, the Farey walk and the certificates use only the 2^71 floor and the rational
  enclosure of delta.

## What the proof actually needs (step 1)

- **Finite part (cheap).** For `Kceil <= K < Kc`, Lemma 7 gives `Lambda < 222 * 2^-1161`.
  - One Farey pair `a/b < delta < c/d` with `b + d > Kc` closes this range, as does any convergent
    pair of log2 3. Every p/K with K < b + d lies outside (a/b, c/d), so
    `|p - K delta| >= K * min(delta - a/b, c/d - delta)`, which is about `1/Kc`.
  - This uses the existing `chain_step` / Farey machinery and a higher-precision delta enclosure. No walk
    and no new shapes are needed above `Kceil`.
  - Kc = 1e120 takes 236 partial quotients (Stern-Brocot path length 2315) and a delta enclosure to about
    1e-240: logSum at 1/2 and 1/3 with roughly 800 and 500 terms, `decide +kernel`, as in
    `LogTwoThreeBounds80`.
- **Infinite tail (the real obstacle).** For `K >= Kc` we need `Lambda > 2m 2^(-K/G_m)`, that is,
  `Lambda > exp(-eps K)` with `eps = ln2/G_111 = 2.5e-23`.
  - A bound `Lambda > c K^-nu` valid for `K >= K0` (with `K0 <= Kc`) suffices whenever
    `nu ln Kc + ln(222/c) < eps Kc`. With Kc = 1e120 this allows **any nu up to about 1e95**, and any
    explicit c and K0 up to 1e120.
  - So the exponent and constant are irrelevant. What matters is **effectivity**: some explicit
    linear-forms lower bound for p log 2 - K log 3, valid for all large K.
  - No finite computation can replace it. Without it nothing bounds K for an m-cycle; Steiner and
    Simons-de Weger needed Baker or Rhin for exactly this reason.
- **No trivial bound works.** `|2^p - 3^K| >= 1` gives only `Lambda >~ 3^-K = exp(-1.1 K)`.
  Ellison-type bounds give `exp(-K/10)`, and those already need Baker. The required rate is 2.5e-23 K.

## Feasibility checks of elementary Pade routes (scripts here)

- `need.py` computes G_m, eps, and the continued fraction of log2 3.
- `scan.py` runs exact sympy computations of type-I integrals `int_0^1 t^an (1-t)^bn / ((1+t)^cn (2+t)^dn)`
  (forms in 1, log 2, log 3/2) over 12 small (a,b,c,d), at n = 6 and 10.
  - Every case has decay rate alpha below coefficient growth beta, once the exact denominators are
    included.
  - The type-I three-form argument needs alpha > beta, so all of them fail.
- By hand, type-II Angelesco simultaneous approximations also fail (alpha_eff < 0):
  - intervals [-1/2,0], [0,1/2]: error about e^-2.7n against denominators about e^5.5n;
  - log(9/8), log(256/243): about e^-7.9n against e^21n.
  - The power-of-2 and power-of-3 denominators dominate.
- This is why Rhin (1987) needed a refined construction with prime-power denominator savings. Even then
  the margin is thin (nu = 13.3).

## Candidate routes for the tail, with cost

1. **Rhin / Hata / Wu-style Pade** (type I, three consecutive forms).
   - Needs:
     - an integral family with alpha > beta under *provable* LCM bounds;
     - exact integrality with p-adic denominator savings;
     - crude sup-norm estimates;
     - nonvanishing of the 3x3 determinant of consecutive forms, through a recurrence or Casoratian proved
       by a creative-telescoping certificate.
   - Mathlib gives `primorial <= 4^n` (LCM rate ln 4 = 1.39 instead of 1). That likely destroys Rhin's
     margin, so a Chebyshev-type psi(x) <= 1.04x (Rosser-Schoenfeld) may have to be formalised too.
   - Estimate: 4-10 weeks of Lean, with a real chance it does not close. The math risk is in finding a
     family that survives crude bounds.
2. **Two-log Baker via Laurent interpolation determinants, or Gelfond's method.**
   - Explicit constants are allowed to be terrible here.
   - Mathlib has Siegel's lemma and maximum-modulus results. Missing are the analytic Schwarz-lemma
     estimates and the zero estimate (nonvanishing of the determinant).
   - Estimate: 6-12+ weeks; no exponent tuning needed.
3. **Intermediate, cheap, and not the goal.** Replace `RhinBound` by a much weaker, cleaner hypothesis:
   `EffMeasure`: there exist explicit nu <= 1e90, c > 0 and K0 <= 1e120 with
   `p log 2 - K log 3 > c K^-nu` for every K >= K0 and p (statement over all integers, not cycles).
   - Proved from it: the finite range by one Farey pair, and the per-m ceilings unchanged.
   - Cost: about 2-4 days.
   - The theorem would then rest on "log 3/log 2 has *some* effective irrationality measure". Every known
     measure (Rhin, Wu, LMN) implies this with huge room. It is still a hypothesis.

Recommendation is in the step-1 report to the coordinator: route 3 now as a cheap de-risking step and
interface, then route 1 or 2 only if Lee accepts a multi-week, about 20-35% lane.

## Lean trust items (coordinator request, 2026-11-03)

- **Toolchain:** `lean-toolchain` = `leanprover/lean4:v4.35.0-rc3`; Mathlib rev c55e6e786f49...
- **Known kernel soundness bugs, July-Oct 2026:**
  - #14576, the Kumar "Collatz disproof": fixed in v4.32.2.
  - #14807 and #14838: fixed in v4.34.0.
  - #15241, #15289 and #15288 (refcount and sharing UB; need adversarial or >100 GB inputs): in v4.35.0
    final (2026-10-12) and backported to v4.34.1.
  - v4.35.0-rc3 includes everything up to v4.34.0. The rc number alone does not show whether it has the
    three v4.35.0 fixes. They matter for untrusted proof terms; our proofs are our own code.
  - v4.34.1 (all fixes) is installed locally.
  - Moving to v4.35.0 final needs a matching Mathlib cache, which was not checked.
- **Independent checkers:** the official v4.35.0-rc3 toolchain ships `leanchecker`,
  `leanchecker-paranoid`, `lean4lean`, `nanoda_bin` and `con-leche`, so no extra downloads are needed.
  This repo has no `.lake` build in place, so nothing was replayed. Replaying applies once a no-Rhin
  theorem exists.
