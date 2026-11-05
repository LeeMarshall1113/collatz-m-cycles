import Mathlib

/-!
# Effective Gelfond method for `log 2`, `log 3`: definitions and elementary lemmas

Route 2G of `computed/target14_norhin/PADE-PLAN.md`. Notation:

* `w i = i₁ log 2 + i₂ log 3`, for `i = (i₁, i₂) ∈ [0,L)²`, are the exponents;
* `auxF c z = Σ c_i exp(w_i z)` is the auxiliary function (integer coefficients `c`);
* `Psi p K c l m = Σ c_i u_i^m 2^{i₁ l} 3^{i₂ l}` with `u_i = i₁ K + i₂ p` is the integer that
  approximates `(K / log 2)^m F^{(m)}(l)`;
* `Lam p K = p log 2 − K log 3`.

Lemmas: L0 (`one_third_le_abs_lam_of_range`), L1 (`iteratedDeriv_auxF`, `differentiable_auxF`,
`norm_auxF_le`), L3 (`approx`), L8 (`sep`, `sep_w`).

The scheme follows the classical Gelfond method. Where pieces are later ported from
M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem* (arXiv 2603.24823,
Lean 4), the file header says so.
-/

namespace Collatz.Gelfond

open Finset Complex

/-- Index set of the exponents. -/
abbrev Idx (L : ℕ) := Fin L × Fin L

/-- The exponent `w_i = i₁ log 2 + i₂ log 3`. -/
noncomputable def w {L : ℕ} (i : Idx L) : ℝ :=
  ((i.1 : ℕ) : ℝ) * Real.log 2 + ((i.2 : ℕ) : ℝ) * Real.log 3

/-- The integer `u_i = i₁ K + i₂ p`, with `K w_i = log 2 · u_i − i₂ Λ`. -/
def u {L : ℕ} (p K : ℕ) (i : Idx L) : ℤ := ((i.1 : ℕ) * K + (i.2 : ℕ) * p : ℕ)

/-- The auxiliary function `F(z) = Σ c_i exp(w_i z)`. -/
noncomputable def auxF {L : ℕ} (c : Idx L → ℤ) (z : ℂ) : ℂ :=
  ∑ i, (c i : ℂ) * Complex.exp ((w i : ℂ) * z)

/-- The integers `Ψ(l, m) = Σ c_i u_i^m 2^{i₁ l} 3^{i₂ l}`. -/
def Psi {L : ℕ} (p K : ℕ) (c : Idx L → ℤ) (l m : ℕ) : ℤ :=
  ∑ i, c i * u p K i ^ m * (2 : ℤ) ^ ((i.1 : ℕ) * l) * (3 : ℤ) ^ ((i.2 : ℕ) * l)

/-- The linear form `Λ = p log 2 − K log 3`. -/
noncomputable def Lam (p K : ℕ) : ℝ := (p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3

/-! ### L0: the range reduction -/

/-- **L0.** Outside `K ≤ p ≤ 2K` the form is large. -/
theorem one_third_le_abs_lam_of_range {p K : ℕ} (hK : 1 ≤ K) (h : p < K ∨ 2 * K < p) :
    (1 / 3 : ℝ) ≤ |Lam p K| := by
  sorry

/-! ### L1: the auxiliary function -/

/-- **L1a.** Derivatives of `F`. -/
theorem iteratedDeriv_auxF {L : ℕ} (c : Idx L → ℤ) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (auxF c) z = ∑ i, (c i : ℂ) * (w i : ℂ) ^ m * Complex.exp ((w i : ℂ) * z) := by
  sorry

/-- **L1b.** `F` is entire. -/
theorem differentiable_auxF {L : ℕ} (c : Idx L → ℤ) : Differentiable ℂ (auxF c) := by
  unfold auxF
  fun_prop

/-- **L1c.** Growth: `|F(z)| ≤ L² C exp(9/5 · L |z|)` when `|c_i| ≤ C`. -/
theorem norm_auxF_le {L : ℕ} (c : Idx L → ℤ) {C : ℝ} (hc : ∀ i, |(c i : ℝ)| ≤ C) (z : ℂ) :
    ‖auxF c z‖ ≤ (L : ℝ) ^ 2 * C * Real.exp (9 / 5 * L * ‖z‖) := by
  sorry

/-! ### L3: the integer approximants -/

/-- **L3.** `|K^m F^{(m)}(l) − (log 2)^m Ψ(l,m)| ≤ L² C · m · L |Λ| (3LK)^m 6^{L l}`. -/
theorem approx {L p K : ℕ} (hpK : p ≤ 2 * K) (c : Idx L → ℤ) {C : ℝ} (hc : ∀ i, |(c i : ℝ)| ≤ C)
    (l m : ℕ) :
    ‖(K : ℂ) ^ m * iteratedDeriv m (auxF c) (l : ℂ) -
        ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi p K c l m : ℂ)‖ ≤
      (L : ℝ) ^ 2 * C * m * L * |Lam p K| * (3 * L * K) ^ m * 6 ^ (L * l) := by
  sorry

/-! ### L8: separation of the exponents -/

/-- **L8.** `|a log 2 + b log 3| ≥ 36^{−L}` for `(a, b) ≠ 0`, `|a|, |b| ≤ L`. -/
theorem sep {L : ℕ} (hL : 1 ≤ L) (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) (ha : |a| ≤ L) (hb : |b| ≤ L) :
    (1 / 36 : ℝ) ^ L ≤ |(a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3| := by
  sorry

/-- Distinct exponents are `36^{−L}`-separated. -/
theorem sep_w {L : ℕ} (hL : 1 ≤ L) {i j : Idx L} (hij : i ≠ j) :
    (1 / 36 : ℝ) ^ L ≤ |w i - w j| := by
  sorry

end Collatz.Gelfond
