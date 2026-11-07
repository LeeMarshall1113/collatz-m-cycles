import Collatz.NoRhin

/-!
# The m ≤ 111 statement without `RhinBound`

Run: `lake env lean scripts/StatementNoRhin.lean`. The only hypotheses are Bařina's verification
bound `2⁷¹` and `EffMeasure` (`Collatz/EffMeasure.lean`), spelled out below.
-/

open Collatz

example :
    EffMeasure =
      ∀ p K : ℕ, 10 ^ 36 ≤ K →
        Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| := rfl

/-- **Main theorem, no `RhinBound`.** If every positive integer up to `2^71` reaches 1 and
`|p log 2 − K log 3| > exp(−K/2⁸⁰)` for all `K ≥ 10³⁶`, every positive `T`-cycle other than
`1 → 2 → 1` has at least 112 local minima. -/
theorem main_statement_111_noRhin
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hE : EffMeasure) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 112 ≤ numLocalMin x p :=
  no_111_cycle_2_71_eff hX hE

#print axioms main_statement_111_noRhin

/-- The hypothesis is implied by a Rhin-type measure (sanity check of its weakness). -/
example (h : RhinAll) : EffMeasure := effMeasure_of_rhinAll h

#print axioms effMeasure_of_rhinAll
