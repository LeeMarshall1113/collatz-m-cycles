import Collatz

/-!
# The statement, spelled out

This file restates the main theorem with every hypothesis written in full and checks that
`Collatz.no_101_cycle_2_71` proves exactly this. Run: `lake env lean scripts/Statement.lean`.

* `T n = n / 2` for even `n` and `(3n + 1) / 2` for odd `n` (`Collatz/Defs.lean`);
* `Reaches T n 1 ↔ ∃ k, T^[k] n = 1` (`Collatz/Defs.lean`);
* `numLocalMin x p` counts the `i < p` such that `T^[i] x` is odd and its cyclic predecessor
  `T^[i + p - 1] x` is even (`Collatz/Statements.lean`);
* `RhinBound` is Simons–de Weger's Lemma 12 (from Rhin's measure), restricted to cycles
  (`Collatz/HercherRhin.lean`).
-/

open Collatz

example : Reaches T = fun n m => ∃ k, T^[k] n = m := rfl

example (x p : ℕ) :
    numLocalMin x p =
      ((Finset.range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0)).card := rfl

example :
    RhinBound =
      ∀ x p : ℕ, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 1 ≤ oddCount T x p →
        Real.exp (-(133 / 10 * (46057 / 100000 + Real.log (oddCount T x p)))) <
          (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 := rfl

/-- **Main theorem.** If every positive integer up to `2^71` reaches 1 and `RhinBound` holds, every
positive `T`-cycle other than `1 → 2 → 1` has at least 102 local minima. -/
theorem main_statement
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 102 ≤ numLocalMin x p :=
  no_101_cycle_2_71 hX hR

#print axioms main_statement

/-- **Extension to `m = 102`.** Same hypotheses: every positive `T`-cycle other than `1 → 2 → 1` has
at least 103 local minima. -/
theorem main_statement_102
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 103 ≤ numLocalMin x p :=
  no_102_cycle_2_71 hX hR

#print axioms main_statement_102

/-- **Extension to `m = 103`.** Same hypotheses: every positive `T`-cycle other than `1 → 2 → 1` has
at least 104 local minima. -/
theorem main_statement_103
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 104 ≤ numLocalMin x p :=
  no_103_cycle_2_71 hX hR

#print axioms main_statement_103

/-- **Extension to `m = 105`** (three-rise chain). Same hypotheses: every positive `T`-cycle other
than `1 → 2 → 1` has at least 106 local minima. -/
theorem main_statement_105
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 106 ≤ numLocalMin x p :=
  no_105_cycle_2_71 hX hR

#print axioms main_statement_105

/-- **Extension to `m = 106`** (three-rise chain). Same hypotheses: every positive `T`-cycle other
than `1 → 2 → 1` has at least 107 local minima. -/
theorem main_statement_106
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 107 ≤ numLocalMin x p :=
  no_106_cycle_2_71 hX hR

#print axioms main_statement_106

/-- **Extension to `m = 107`** (three-rise chain). Same hypotheses: every positive `T`-cycle other
than `1 → 2 → 1` has at least 108 local minima. -/
theorem main_statement_107
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 108 ≤ numLocalMin x p :=
  no_107_cycle_2_71 hX hR

#print axioms main_statement_107

/-- **Extension to `m = 108`** (three-rise chain). Same hypotheses: every positive `T`-cycle other
than `1 → 2 → 1` has at least 109 local minima. -/
theorem main_statement_108
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) (hR : RhinBound) :
    ∀ x p, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 → 109 ≤ numLocalMin x p :=
  no_108_cycle_2_71 hX hR

#print axioms main_statement_108
