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
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have h32 : Real.log 3 - Real.log 2 ≥ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this
    linarith
  have h43 : Real.log 3 - 2 * Real.log 2 ≤ -(1 / 4) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at this
    linarith
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rcases h with h | h
  · have hp : (p : ℝ) + 1 ≤ K := by exact_mod_cast h
    have : -Lam p K ≥ 1 / 3 := by
      unfold Lam
      nlinarith
    exact le_trans this (neg_le_abs _)
  · have hp : 2 * (K : ℝ) + 1 ≤ p := by exact_mod_cast h
    have : Lam p K ≥ 1 / 3 := by
      unfold Lam
      nlinarith
    exact le_trans this (le_abs_self _)

/-! ### L1: the auxiliary function -/

/-- **L1a.** Derivatives of `F`. -/
theorem iteratedDeriv_auxF {L : ℕ} (c : Idx L → ℤ) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (auxF c) z = ∑ i, (c i : ℂ) * (w i : ℂ) ^ m * Complex.exp ((w i : ℂ) * z) := by
  have key : ∀ n : ℕ, iteratedDeriv n (auxF c) =
      fun z => ∑ i, (c i : ℂ) * (w i : ℂ) ^ n * Complex.exp ((w i : ℂ) * z) := by
    intro n
    induction n with
    | zero => funext z; simp [auxF]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      have hd : HasDerivAt (fun z : ℂ => ∑ i, (c i : ℂ) * (w i : ℂ) ^ n * Complex.exp ((w i : ℂ) * z))
          (∑ i, (c i : ℂ) * (w i : ℂ) ^ n * (Complex.exp ((w i : ℂ) * z) * ((w i : ℂ) * 1))) z := by
        apply HasDerivAt.fun_sum
        intro i _
        exact (((hasDerivAt_id z).const_mul (w i : ℂ)).cexp).const_mul ((c i : ℂ) * (w i : ℂ) ^ n)
      rw [hd.deriv]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  rw [key]

/-- **L1b.** `F` is entire. -/
theorem differentiable_auxF {L : ℕ} (c : Idx L → ℤ) : Differentiable ℂ (auxF c) := by
  unfold auxF
  fun_prop

/-- `log 6 ≤ 9/5`. -/
theorem log2_add_log3_le : Real.log 2 + Real.log 3 ≤ 9 / 5 := by
  rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
  have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 5 by norm_num) 8
  refine le_trans ?_ this
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The exponents lie in `[0, 9L/5]`. -/
theorem w_bounds {L : ℕ} (i : Idx L) : 0 ≤ w i ∧ w i ≤ 9 / 5 * L := by
  have hlog6 := log2_add_log3_le
  have h1 : ((i.1 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.1.isLt.le
  have h2 : ((i.2 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.2.isLt.le
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have n1 : (0 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ((i.2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  unfold w
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right h1 l2.le, mul_le_mul_of_nonneg_right h2 l3.le,
      mul_le_mul_of_nonneg_left hlog6 hL0]

/-- Power-difference bound. -/
theorem pow_diff_le {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hR : R = 0 ∨ 1 ≤ R) (m : ℕ) : |a ^ m - b ^ m| ≤ m * |a - b| * R ^ m := by
  rcases hR with rfl | h1
  · have h1 : a = 0 := le_antisymm haR ha
    have h2 : b = 0 := le_antisymm hbR hb
    subst h1 h2
    simp
  · have hR0 : 0 ≤ R := by linarith
    rcases m with _ | m
    · simp
    · rw [show a ^ (m + 1) - b ^ (m + 1) = _ from (geom_sum₂_mul a b (m + 1)).symm, abs_mul]
      have hs : |∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m + 1 - 1 - i)| ≤
          (m + 1) * R ^ (m + 1) := by
        calc _ ≤ ∑ i ∈ Finset.range (m + 1), |a ^ i * b ^ (m + 1 - 1 - i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range (m + 1), R ^ (m + 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]
              have hi' : i < m + 1 := Finset.mem_range.mp hi
              calc a ^ i * b ^ (m + 1 - 1 - i) ≤ R ^ i * R ^ (m + 1 - 1 - i) :=
                    mul_le_mul (pow_le_pow_left₀ ha haR _) (pow_le_pow_left₀ hb hbR _)
                      (pow_nonneg hb _) (pow_nonneg hR0 _)
                _ = R ^ m := by rw [← pow_add]; congr 1; omega
                _ ≤ R ^ (m + 1) := pow_le_pow_right₀ h1 (Nat.le_succ m)
          _ = (m + 1) * R ^ (m + 1) := by simp
      calc _ ≤ ((m + 1) * R ^ (m + 1)) * |a - b| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        _ = ((m + 1 : ℕ) : ℝ) * |a - b| * R ^ (m + 1) := by push_cast; ring

/-- **L1c.** Growth: `|F(z)| ≤ L² C exp(9/5 · L |z|)` when `|c_i| ≤ C`. -/
theorem norm_auxF_le {L : ℕ} (c : Idx L → ℤ) {C : ℝ} (hc : ∀ i, |(c i : ℝ)| ≤ C) (z : ℂ) :
    ‖auxF c z‖ ≤ (L : ℝ) ^ 2 * C * Real.exp (9 / 5 * L * ‖z‖) := by
  have hw := w_bounds (L := L)
  calc ‖auxF c z‖ ≤ ∑ i, ‖(c i : ℂ) * Complex.exp ((w i : ℂ) * z)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Idx L, C * Real.exp (9 / 5 * L * ‖z‖) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, Complex.norm_exp]
      have hci : ‖(c i : ℂ)‖ ≤ C := by
        simpa [Complex.norm_intCast] using hc i
      have hC : 0 ≤ C := (norm_nonneg _).trans hci
      refine mul_le_mul hci (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC
      rw [Complex.re_ofReal_mul]
      calc w i * z.re ≤ w i * ‖z‖ :=
            mul_le_mul_of_nonneg_left (Complex.re_le_norm z) (hw i).1
        _ ≤ 9 / 5 * L * ‖z‖ := mul_le_mul_of_nonneg_right (hw i).2 (norm_nonneg _)
    _ = (L : ℝ) ^ 2 * C * Real.exp (9 / 5 * L * ‖z‖) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

/-! ### L3: the integer approximants -/

/-- **L3.** `|K^m F^{(m)}(l) − (log 2)^m Ψ(l,m)| ≤ L² C · m · L |Λ| (3LK)^m 6^{L l}`. -/
theorem approx {L p K : ℕ} (hpK : p ≤ 2 * K) (c : Idx L → ℤ) {C : ℝ} (hc : ∀ i, |(c i : ℝ)| ≤ C)
    (l m : ℕ) :
    ‖(K : ℂ) ^ m * iteratedDeriv m (auxF c) (l : ℂ) -
        ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi p K c l m : ℂ)‖ ≤
      (L : ℝ) ^ 2 * C * m * L * |Lam p K| * (3 * L * K) ^ m * 6 ^ (L * l) := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hp : (p : ℝ) ≤ 2 * K := by exact_mod_cast hpK
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l2le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hRcase : (3 * (L : ℝ) * K = 0) ∨ (1 ≤ 3 * (L : ℝ) * K) := by
    by_cases h : 3 * L * K = 0
    · left
      have : ((3 * L * K : ℕ) : ℝ) = 0 := by rw [h]; simp
      push_cast at this
      exact this
    · right
      have : 1 ≤ 3 * L * K := Nat.one_le_iff_ne_zero.mpr h
      have h' : ((1 : ℕ) : ℝ) ≤ ((3 * L * K : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
  have hEr : ∀ i : Idx L, Real.exp (w i * l) =
      (2 : ℝ) ^ ((i.1 : ℕ) * l) * 3 ^ ((i.2 : ℕ) * l) := by
    intro i
    have : w i * l = (((i.1 : ℕ) * l : ℕ) : ℝ) * Real.log 2 +
        (((i.2 : ℕ) * l : ℕ) : ℝ) * Real.log 3 := by
      unfold w; push_cast; ring
    rw [this, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num),
      Real.exp_log (by norm_num)]
  have hEc : ∀ i : Idx L, Complex.exp ((w i : ℂ) * (l : ℂ)) =
      (2 : ℂ) ^ ((i.1 : ℕ) * l) * (3 : ℂ) ^ ((i.2 : ℕ) * l) := by
    intro i
    have h := congrArg (fun x : ℝ => (x : ℂ)) (hEr i)
    simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] at h
    exact h
  have expr : (K : ℂ) ^ m * iteratedDeriv m (auxF c) (l : ℂ) -
      ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi p K c l m : ℂ) =
      ((∑ i : Idx L, (c i : ℝ) * (((K : ℝ) * w i) ^ m - (Real.log 2 * (u p K i : ℝ)) ^ m) *
        ((2 : ℝ) ^ ((i.1 : ℕ) * l) * 3 ^ ((i.2 : ℕ) * l)) : ℝ) : ℂ) := by
    rw [iteratedDeriv_auxF]
    push_cast [Psi]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hEc i]
    simp only [mul_pow]
    simp only [u]
    push_cast
    ring
  rw [expr, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∑ i : Idx L, |(c i : ℝ) * (((K : ℝ) * w i) ^ m - (Real.log 2 * (u p K i : ℝ)) ^ m) *
        ((2 : ℝ) ^ ((i.1 : ℕ) * l) * 3 ^ ((i.2 : ℕ) * l))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Idx L, C * (m * (L * |Lam p K|) * (3 * (L : ℝ) * K) ^ m) * 6 ^ (L * l) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hci := hc i
      have hC : 0 ≤ C := (abs_nonneg _).trans hci
      have hi1 : ((i.1 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.1.isLt.le
      have hi2 : ((i.2 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.2.isLt.le
      have n1 : (0 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have n2 : (0 : ℝ) ≤ ((i.2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hu : ((u p K i : ℤ) : ℝ) = ((i.1 : ℕ) : ℝ) * K + ((i.2 : ℕ) : ℝ) * p := by
        simp [u]
      have hw := w_bounds i
      have hu0 : (0 : ℝ) ≤ (u p K i : ℝ) := by rw [hu]; positivity
      have hu1 : (u p K i : ℝ) ≤ 3 * L * K := by
        rw [hu]
        nlinarith [mul_le_mul_of_nonneg_right hi1 hK0, mul_le_mul hi2 hp hp0 hL0]
      have ha0 : 0 ≤ (K : ℝ) * w i := mul_nonneg hK0 hw.1
      have ha1 : (K : ℝ) * w i ≤ 3 * L * K := by
        nlinarith [mul_le_mul_of_nonneg_left hw.2 hK0]
      have hb0 : 0 ≤ Real.log 2 * (u p K i : ℝ) := mul_nonneg l2.le hu0
      have hb1 : Real.log 2 * (u p K i : ℝ) ≤ 3 * L * K := by
        nlinarith [mul_le_mul l2le hu1 hu0 zero_le_one]
      have hab := pow_diff_le ha0 hb0 ha1 hb1 hRcase m
      have hdiff : |(K : ℝ) * w i - Real.log 2 * (u p K i : ℝ)| ≤ L * |Lam p K| := by
        have : (K : ℝ) * w i - Real.log 2 * (u p K i : ℝ) = -((i.2 : ℕ) : ℝ) * Lam p K := by
          rw [hu]; unfold w Lam; ring
        rw [this, abs_mul, abs_neg, abs_of_nonneg n2]
        exact mul_le_mul_of_nonneg_right hi2 (abs_nonneg _)
      have hD : |((K : ℝ) * w i) ^ m - (Real.log 2 * (u p K i : ℝ)) ^ m| ≤
          m * (L * |Lam p K|) * (3 * (L : ℝ) * K) ^ m := by
        refine hab.trans ?_
        have hR0 : 0 ≤ 3 * (L : ℝ) * K := by positivity
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff hm0) (pow_nonneg hR0 _)
      have hE : |(2 : ℝ) ^ ((i.1 : ℕ) * l) * 3 ^ ((i.2 : ℕ) * l)| ≤ 6 ^ (L * l) := by
        rw [abs_of_nonneg (by positivity)]
        have h1 : (2 : ℝ) ^ ((i.1 : ℕ) * l) ≤ 2 ^ (L * l) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ i.1.isLt.le)
        have h2 : (3 : ℝ) ^ ((i.2 : ℕ) * l) ≤ 3 ^ (L * l) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ i.2.isLt.le)
        calc _ ≤ (2 : ℝ) ^ (L * l) * 3 ^ (L * l) := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 6 ^ (L * l) := by rw [← mul_pow]; norm_num
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hci hD (abs_nonneg _) hC) hE (abs_nonneg _)
        (mul_nonneg hC (by positivity))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

/-! ### L8: separation of the exponents -/

/-- **L8.** `|a log 2 + b log 3| ≥ 36^{−L}` for `(a, b) ≠ 0`, `|a|, |b| ≤ L`. -/
theorem sep {L : ℕ} (hL : 1 ≤ L) (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) (ha : |a| ≤ L) (hb : |b| ≤ L) :
    (1 / 36 : ℝ) ^ L ≤ |(a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3| := by
  set A : ℕ := 2 ^ a.toNat * 3 ^ b.toNat with hA
  set B : ℕ := 2 ^ (-a).toNat * 3 ^ (-b).toNat with hB
  have habs := abs_le.mp ha
  have hbbs := abs_le.mp hb
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hA6 : A ≤ 6 ^ L := by
    have h1 : 2 ^ a.toNat ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ b.toNat ≤ 3 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc A ≤ 2 ^ L * 3 ^ L := Nat.mul_le_mul h1 h2
      _ = 6 ^ L := by rw [← mul_pow]; norm_num
  have hB6 : B ≤ 6 ^ L := by
    have h1 : 2 ^ (-a).toNat ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ (-b).toNat ≤ 3 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc B ≤ 2 ^ L * 3 ^ L := Nat.mul_le_mul h1 h2
      _ = 6 ^ L := by rw [← mul_pow]; norm_num
  have hne : A ≠ B := by
    intro hAB
    have h2 := congrArg (fun n => Nat.factorization n 2) hAB
    have h3 := congrArg (fun n => Nat.factorization n 3) hAB
    simp [hA, hB, Nat.factorization_mul, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization Nat.prime_three] at h2 h3
    omega
  have hx : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 = Real.log A - Real.log B := by
    have e1 : Real.log A = (a.toNat : ℝ) * Real.log 2 + (b.toNat : ℝ) * Real.log 3 := by
      rw [hA]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have e2 : Real.log B = ((-a).toNat : ℝ) * Real.log 2 + ((-b).toNat : ℝ) * Real.log 3 := by
      rw [hB]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have ea : (a : ℝ) = (a.toNat : ℝ) - ((-a).toNat : ℝ) := by
      exact_mod_cast (Int.toNat_sub_toNat_neg a).symm
    have eb : (b : ℝ) = (b.toNat : ℝ) - ((-b).toNat : ℝ) := by
      exact_mod_cast (Int.toNat_sub_toNat_neg b).symm
    rw [e1, e2, ea, eb]; ring
  have gap : ∀ U V : ℕ, 0 < V → V < U → U ≤ 6 ^ L →
      (1 / 36 : ℝ) ^ L ≤ Real.log U - Real.log V := by
    intro U V hV hVU hU
    have hVr : (0 : ℝ) < V := by exact_mod_cast hV
    have hUr : (0 : ℝ) < U := by exact_mod_cast hV.trans hVU
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (V : ℝ) / U by positivity)
    rw [Real.log_div hVr.ne' hUr.ne'] at h1
    have h2 : (1 : ℝ) / U ≤ 1 - (V : ℝ) / U := by
      rw [div_le_iff₀ hUr, sub_mul, div_mul_cancel₀ _ hUr.ne']
      have : (V : ℝ) + 1 ≤ U := by exact_mod_cast hVU
      linarith
    have h3 : (1 / 36 : ℝ) ^ L ≤ 1 / (U : ℝ) := by
      have hU' : (U : ℝ) ≤ 6 ^ L := by exact_mod_cast hU
      have h4 : (1 / 36 : ℝ) ^ L ≤ (1 / 6 : ℝ) ^ L :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) L
      calc (1 / 36 : ℝ) ^ L ≤ (1 / 6 : ℝ) ^ L := h4
        _ = 1 / 6 ^ L := by rw [one_div, inv_pow, one_div]
        _ ≤ 1 / U := one_div_le_one_div_of_le hUr hU'
    linarith
  rw [hx]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_sub_comm, abs_of_nonneg]
    · exact gap B A hApos h hB6
    · have := gap B A hApos h hB6
      have : (0 : ℝ) ≤ (1 / 36 : ℝ) ^ L := by positivity
      linarith
  · rw [abs_of_nonneg]
    · exact gap A B hBpos h hA6
    · have := gap A B hBpos h hA6
      have : (0 : ℝ) ≤ (1 / 36 : ℝ) ^ L := by positivity
      linarith

/-- Distinct exponents are `36^{−L}`-separated. -/
theorem sep_w {L : ℕ} (hL : 1 ≤ L) {i j : Idx L} (hij : i ≠ j) :
    (1 / 36 : ℝ) ^ L ≤ |w i - w j| := by
  have hi1 := i.1.isLt
  have hi2 := i.2.isLt
  have hj1 := j.1.isLt
  have hj2 := j.2.isLt
  have key := sep hL (((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ)) (((i.2 : ℕ) : ℤ) - ((j.2 : ℕ) : ℤ))
    (by
      by_contra hcon
      push Not at hcon
      apply hij
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    (by rw [abs_le]; constructor <;> omega) (by rw [abs_le]; constructor <;> omega)
  have e : w i - w j = (((((i.1 : ℕ) : ℤ) - ((j.1 : ℕ) : ℤ) : ℤ)) : ℝ) * Real.log 2 +
      (((((i.2 : ℕ) : ℤ) - ((j.2 : ℕ) : ℤ) : ℤ)) : ℝ) * Real.log 3 := by
    unfold w; push_cast; ring
  rw [e]; exact key

end Collatz.Gelfond
