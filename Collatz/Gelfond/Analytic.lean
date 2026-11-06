import Mathlib

/-!
# Generic analytic lemmas for the Gelfond method

* L4 `hermite`: Hermite interpolation at the integer nodes `0, …, h−1` with multiplicity `M`, with a
  growth bound from Newton's divided differences: every divided difference is at most `2^k ε`
  because distinct nodes are at distance at least 1.
* L5 `schwarz`: if an entire `g` has zeros of order `M` at `0, …, h−1`, then on `|z| ≤ R`
  we have `|g(z)| ≤ S · Π |z − l|^M / (R − h)^{hM}`. The function `g / Π (z − l)^M` is entire, so
  the maximum modulus principle applies.

The removable-singularity part of L5 may be ported from M. Karatarakis and F. Wiedijk, *A
formalization of the Gelfond–Schneider theorem* (arXiv 2603.24823); credit to be recorded here when
it is.
-/

namespace Collatz.Gelfond

open Finset Complex

section Hermite
open Polynomial

/-- Taylor polynomial of the data `D l ·` at the node `l`, of degree `k`. -/
noncomputable def hermTaylor (D : ℕ → ℕ → ℂ) (l k : ℕ) : ℂ[X] :=
  ∑ t ∈ range (k + 1), C (D l t / (t.factorial : ℂ)) * (X - C (l : ℂ)) ^ t

/-- Confluent interpolant (Neville recursion) for the node window `i, …, i+k` of the node
sequence `j ↦ j / M`. -/
noncomputable def hermQ (M : ℕ) (D : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ[X]
  | i, 0 => hermTaylor D (i / M) 0
  | i, k + 1 =>
    if i / M = (i + k + 1) / M then hermTaylor D (i / M) (k + 1)
    else C ((((i + k + 1) / M : ℕ) : ℂ) - ((i / M : ℕ) : ℂ))⁻¹ *
      ((X - C ((i / M : ℕ) : ℂ)) * hermQ M D (i + 1) k -
        (X - C (((i + k + 1) / M : ℕ) : ℂ)) * hermQ M D i k)

/-- Multiplicity of the node `l` in the window `i, …, i+k`. -/
def hermMu (M l i k : ℕ) : ℕ := ∑ t ∈ range (k + 1), if (i + t) / M = l then 1 else 0

theorem hermTaylor_jet (D : ℕ → ℕ → ℂ) (l k m : ℕ) (hm : m ≤ k) :
    (derivative^[m] (hermTaylor D l k)).eval (l : ℂ) = D l m := by
  unfold hermTaylor
  rw [iterate_derivative_sum, eval_finsetSum]
  have : ∀ t ∈ range (k + 1), (derivative^[m] (C (D l t / (t.factorial : ℂ)) *
      (X - C (l : ℂ)) ^ t)).eval (l : ℂ) = if t = m then D l m else 0 := by
    intro t _
    rw [iterate_derivative_C_mul, iterate_derivative_X_sub_pow]
    simp only [eval_mul, eval_C, eval_natCast, eval_pow, eval_sub, eval_X, sub_self, nsmul_eq_mul]
    by_cases htm : t = m
    · subst htm
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self, ite_true]
      have : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast t.factorial_ne_zero
      field_simp
    · rw [if_neg htm]
      rcases lt_or_gt_of_ne htm with h | h
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp
      · rw [zero_pow (by omega)]; simp
  rw [sum_congr rfl this, sum_ite_eq' (range (k + 1)) m, if_pos (mem_range.mpr (by omega))]

theorem hermLeib (Q : ℂ[X]) (a l : ℂ) (m : ℕ) :
    (derivative^[m] ((X - C a) * Q)).eval l =
      (l - a) * (derivative^[m] Q).eval l + (m : ℂ) * (derivative^[m - 1] Q).eval l := by
  have e : (X - C a) * Q = Q * X - C a * Q := by ring
  rw [e, iterate_derivative_sub, iterate_derivative_mul_X, iterate_derivative_C_mul]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_natCast, nsmul_eq_mul]
  ring

theorem hermMu_succ_right (M l i k : ℕ) :
    hermMu M l i (k + 1) = hermMu M l i k + if (i + k + 1) / M = l then 1 else 0 := by
  unfold hermMu
  rw [sum_range_succ _ (k + 1)]
  simp [add_assoc]

theorem hermMu_succ_left (M l i k : ℕ) :
    hermMu M l i (k + 1) = hermMu M l (i + 1) k + if i / M = l then 1 else 0 := by
  unfold hermMu
  rw [sum_range_succ' _ (k + 1)]
  simp only [add_zero]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [show i + (t + 1) = i + 1 + t by ring]

theorem hermQ_jet (M : ℕ) (D : ℕ → ℕ → ℂ) :
    ∀ k i l m, m < hermMu M l i k →
      (derivative^[m] (hermQ M D i k)).eval (l : ℂ) = D l m := by
  intro k
  induction k with
  | zero =>
    intro i l m hm
    simp only [hermMu, zero_add, range_one, sum_singleton, add_zero] at hm
    split_ifs at hm with hl
    · have hm0 : m = 0 := by omega
      subst hm0; subst hl
      exact hermTaylor_jet D _ 0 0 le_rfl
    · omega
  | succ k ih =>
    intro i l m hm
    unfold hermQ
    split_ifs with he
    · -- equal ends
      have hall : ∀ t ≤ k + 1, (i + t) / M = i / M := by
        intro t ht
        refine le_antisymm ?_ (Nat.div_le_div_right (by omega))
        rw [he]; exact Nat.div_le_div_right (by omega)
      have hmu : hermMu M l i (k + 1) = if i / M = l then k + 2 else 0 := by
        unfold hermMu
        rw [sum_congr rfl (g := fun _ => if i / M = l then 1 else 0)]
        · simp
        · intro t ht
          rw [hall t (by have := mem_range.mp ht; omega)]
      rw [hmu] at hm
      split_ifs at hm with hl
      · subst hl
        exact hermTaylor_jet D _ _ m (by omega)
      · omega
    · -- Neville step
      set ia := i / M with hia
      set ib := (i + k + 1) / M with hib
      have hδ : (ib : ℂ) - (ia : ℂ) ≠ 0 := by
        intro h0
        exact he (by exact_mod_cast (sub_eq_zero.mp h0).symm)
      have hR := hermMu_succ_right M l i k
      have hL := hermMu_succ_left M l i k
      rw [← hib] at hR
      rw [← hia] at hL
      rw [iterate_derivative_C_mul, eval_mul, iterate_derivative_sub, eval_sub,
        hermLeib, hermLeib]
      simp only [eval_C]
      -- known values
      have F1 : ((l : ℂ) - (ia : ℂ)) * (derivative^[m] (hermQ M D (i + 1) k)).eval (l : ℂ) =
          ((l : ℂ) - (ia : ℂ)) * D l m := by
        by_cases hl : ia = l
        · rw [hl]; simp
        · rw [ih (i + 1) l m (by rw [if_neg hl] at hL; omega)]
      have F2 : ((l : ℂ) - (ib : ℂ)) * (derivative^[m] (hermQ M D i k)).eval (l : ℂ) =
          ((l : ℂ) - (ib : ℂ)) * D l m := by
        by_cases hl : ib = l
        · rw [hl]; simp
        · rw [ih i l m (by rw [if_neg hl] at hR; omega)]
      have F3 : (m : ℂ) * (derivative^[m - 1] (hermQ M D (i + 1) k)).eval (l : ℂ) =
          (m : ℂ) * D l (m - 1) := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp
        · rw [ih (i + 1) l (m - 1) (by
            have : (if ia = l then 1 else 0) ≤ 1 := by split_ifs <;> omega
            omega)]
      have F4 : (m : ℂ) * (derivative^[m - 1] (hermQ M D i k)).eval (l : ℂ) =
          (m : ℂ) * D l (m - 1) := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp
        · rw [ih i l (m - 1) (by
            have : (if ib = l then 1 else 0) ≤ 1 := by split_ifs <;> omega
            omega)]
      rw [F1, F2, F3, F4]
      field_simp
      ring

theorem hermTaylor_bound (D : ℕ → ℕ → ℂ) {ε : ℝ} (M h l k : ℕ) (hl : l < h) (hk : k < M)
    (hD : ∀ l < h, ∀ m < M, ‖D l m‖ ≤ ε) (hε : 0 ≤ ε) (z : ℂ) (hr : 1 ≤ ‖z‖ + h) :
    ‖(hermTaylor D l k).eval z‖ ≤ ε * (k + 1) * (2 * (‖z‖ + h)) ^ k := by
  set r : ℝ := ‖z‖ + h with hrdef
  unfold hermTaylor
  rw [eval_finsetSum]
  refine (norm_sum_le _ _).trans ?_
  have hzl : ‖z - (l : ℂ)‖ ≤ r := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_natCast]
    have : (l : ℝ) ≤ h := by exact_mod_cast hl.le
    linarith
  have hterm : ∀ t ∈ range (k + 1), ‖(C (D l t / (t.factorial : ℂ)) *
      (X - C (l : ℂ)) ^ t).eval z‖ ≤ ε * (2 * r) ^ k := by
    intro t ht
    have htk : t ≤ k := by have := mem_range.mp ht; omega
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, norm_mul, norm_pow, norm_div,
      Complex.norm_natCast]
    have hfac : (1 : ℝ) ≤ t.factorial := by exact_mod_cast t.factorial_pos
    have h1 : ‖D l t‖ / (t.factorial : ℝ) ≤ ε :=
      (div_le_self (norm_nonneg _) hfac).trans (hD l hl t (by omega))
    have h2 : ‖z - (l : ℂ)‖ ^ t ≤ (2 * r) ^ k :=
      (pow_le_pow_left₀ (norm_nonneg _) hzl t).trans
        ((pow_le_pow_right₀ hr htk).trans (pow_le_pow_left₀ (by linarith) (by linarith) k))
    exact mul_le_mul h1 h2 (by positivity) hε
  refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [card_range, nsmul_eq_mul]
  push_cast
  linarith

theorem hermQ_bound (M h : ℕ) (hM : 1 ≤ M) (D : ℕ → ℕ → ℂ) {ε : ℝ}
    (hD : ∀ l < h, ∀ m < M, ‖D l m‖ ≤ ε) (hε : 0 ≤ ε) (z : ℂ) (hr : 1 ≤ ‖z‖ + h) :
    ∀ k i, i + k < h * M → ‖(hermQ M D i k).eval z‖ ≤ ε * (k + 1) * (2 * (‖z‖ + h)) ^ k := by
  set r : ℝ := ‖z‖ + h with hrdef
  have hM0 : 0 < M := hM
  have hlt : ∀ j, j < h * M → j / M < h := fun j hj => (Nat.div_lt_iff_lt_mul hM0).mpr hj
  have hzn : ∀ j, j < h → ‖z - (j : ℂ)‖ ≤ r := by
    intro j hj
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_natCast]
    have : (j : ℝ) ≤ h := by exact_mod_cast hj.le
    linarith
  intro k
  induction k with
  | zero =>
    intro i hi
    simp only [hermQ]
    have := hermTaylor_bound D M h (i / M) 0 (hlt i (by omega)) hM0 hD hε z hr
    simpa using this
  | succ k ih =>
    intro i hi
    unfold hermQ
    split_ifs with he
    · have hkM : k + 1 < M := by
        have h1 : (i + (k + 1)) / M < i / M + 1 := by rw [show i + (k + 1) = i + k + 1 by ring, ← he]; omega
        rw [Nat.div_lt_iff_lt_mul hM0] at h1
        have h2 : i / M * M ≤ i := Nat.div_mul_le_self i M
        have h3 : (i / M + 1) * M = i / M * M + M := by ring
        omega
      have := hermTaylor_bound D M h (i / M) (k + 1) (hlt i (by omega)) hkM hD hε z hr
      simpa using this
    · have hmono : i / M ≤ (i + k + 1) / M := Nat.div_le_div_right (by omega)
      have hne : i / M < (i + k + 1) / M := lt_of_le_of_ne hmono he
      have hδ : ‖(((i + k + 1) / M : ℕ) : ℂ) - ((i / M : ℕ) : ℂ)‖ ≥ 1 := by
        rw [← Nat.cast_sub hmono, Complex.norm_natCast]
        exact_mod_cast Nat.sub_pos_of_lt hne
      have hδ' : ‖((((i + k + 1) / M : ℕ) : ℂ) - ((i / M : ℕ) : ℂ))⁻¹‖ ≤ 1 := by
        rw [norm_inv]; exact inv_le_one_of_one_le₀ hδ
      have B1 := ih (i + 1) (by omega)
      have B2 := ih i (by omega)
      have hza := hzn (i / M) (hlt i (by omega))
      have hzb := hzn ((i + k + 1) / M) (hlt _ (by omega))
      have hB : 0 ≤ ε * (k + 1) * (2 * r) ^ k := by positivity
      simp only [eval_mul, eval_C, eval_sub, eval_X]
      rw [norm_mul]
      have hin : ‖(z - (((i / M : ℕ)) : ℂ)) * (hermQ M D (i + 1) k).eval z -
          (z - ((((i + k + 1) / M : ℕ)) : ℂ)) * (hermQ M D i k).eval z‖ ≤
          2 * r * (ε * (k + 1) * (2 * r) ^ k) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul hza B1 (norm_nonneg _) (by linarith)
        have := mul_le_mul hzb B2 (norm_nonneg _) (by linarith)
        nlinarith
      calc _ ≤ 1 * (2 * r * (ε * (k + 1) * (2 * r) ^ k)) :=
            mul_le_mul hδ' hin (norm_nonneg _) zero_le_one
        _ = ε * (k + 1) * (2 * r) ^ (k + 1) := by ring
        _ ≤ ε * ((k + 1 : ℕ) + 1) * (2 * r) ^ (k + 1) := by
            have : 0 ≤ ε * (2 * r) ^ (k + 1) := by positivity
            push_cast; nlinarith

theorem hermMu_count (M h l : ℕ) (hM : 0 < M) (hl : l < h) : hermMu M l 0 (h * M - 1) = M := by
  have hn : 0 < h * M := Nat.mul_pos (by omega) hM
  unfold hermMu
  rw [Nat.sub_add_cancel hn, ← Finset.card_filter]
  have : (range (h * M)).filter (fun t => (0 + t) / M = l) = Ico (l * M) (l * M + M) := by
    ext t
    simp only [mem_filter, mem_range, mem_Ico, zero_add]
    constructor
    · rintro ⟨ht, he⟩
      have h1 := (Nat.le_div_iff_mul_le hM).mp he.ge
      have h2 := (Nat.div_lt_iff_lt_mul hM).mp (show t / M < l + 1 by omega)
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      have : (l + 1) * M ≤ h * M := Nat.mul_le_mul_right _ hl
      refine ⟨by nlinarith, ?_⟩
      apply le_antisymm
      · have := (Nat.div_lt_iff_lt_mul hM).mpr (show t < (l + 1) * M by nlinarith)
        omega
      · exact (Nat.le_div_iff_mul_le hM).mpr h1
  rw [this]; simp

/-- **L4.** Hermite interpolation with a growth bound. -/
theorem hermite (h M : ℕ) (D : ℕ → ℕ → ℂ) {ε : ℝ} (hD : ∀ l < h, ∀ m < M, ‖D l m‖ ≤ ε)
    (hε : 0 ≤ ε) :
    ∃ P : Polynomial ℂ, (∀ l < h, ∀ m < M, (Polynomial.derivative^[m] P).eval (l : ℂ) = D l m) ∧
      ∀ z : ℂ, ‖P.eval z‖ ≤ ε * (h * M) * (2 * (‖z‖ + h)) ^ (h * M) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · exact ⟨0, by simp, by simp⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, by simp, by simp⟩
  have hn : 0 < h * M := Nat.mul_pos hh hM
  refine ⟨hermQ M D 0 (h * M - 1), ?_, ?_⟩
  · intro l hl m hm
    apply hermQ_jet
    rw [hermMu_count M h l hM hl]
    exact hm
  · intro z
    have hr : (1 : ℝ) ≤ ‖z‖ + h := by
      have : (1 : ℝ) ≤ h := by exact_mod_cast hh
      linarith [norm_nonneg z]
    have hb := hermQ_bound M h hM D hD hε z hr (h * M - 1) 0 (by omega)
    have hc : ((h * M - 1 : ℕ) : ℝ) + 1 = (h : ℝ) * M := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]; push_cast; ring
    rw [hc] at hb
    refine hb.trans ?_
    have hpow : (2 * (‖z‖ + h)) ^ (h * M - 1) ≤ (2 * (‖z‖ + h)) ^ (h * M) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have : 0 ≤ ε * ((h : ℝ) * M) := by positivity
    exact mul_le_mul_of_nonneg_left hpow this
end Hermite

/-- An entire function of analytic order `≥ M` at `a` is `(z-a)^M` times an entire function. -/
theorem schwarz_factor_one (a : ℂ) :
    ∀ (M : ℕ) (f : ℂ → ℂ), Differentiable ℂ f → (M : ℕ∞) ≤ analyticOrderAt f a →
      ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, f z = (z - a) ^ M * q z := by
  intro M
  induction M with
  | zero => intro f hf _; exact ⟨f, hf, fun z => by simp⟩
  | succ M ih =>
    intro f hf hord
    have hfa : f a = 0 := by
      have h1 : analyticOrderAt f a ≠ 0 := by
        intro h0; rw [h0] at hord; simp at hord
      exact (hf.analyticAt a).analyticOrderAt_ne_zero.mp h1
    have hq1 : Differentiable ℂ (dslope f a) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn
    have hfq : f = (fun z => z - a) * dslope f a := by
      funext z
      have := sub_smul_dslope f a z
      simp only [hfa, sub_zero, smul_eq_mul] at this
      simp [this]
    have hord2 : (M : ℕ∞) ≤ analyticOrderAt (dslope f a) a := by
      rw [hfq, analyticOrderAt_mul (by fun_prop) (hq1.analyticAt a),
        analyticOrderAt_id_sub_const_self] at hord
      rw [add_comm] at hord
      have : (M : ℕ∞) + 1 ≤ analyticOrderAt (dslope f a) a + 1 := by
        simpa using hord
      exact (ENat.add_le_add_iff_right (by simp)).mp this
    obtain ⟨q, hq, hqe⟩ := ih _ hq1 hord2
    refine ⟨q, hq, fun z => ?_⟩
    have := congrFun hfq z
    simp only [Pi.mul_apply] at this
    rw [this, hqe z]; ring

/-- Factorization through the nodes `0, …, h-1`. -/
theorem schwarz_factor_finset (M : ℕ) : ∀ (s : Finset ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
    (∀ a ∈ s, (M : ℕ∞) ≤ analyticOrderAt f (a : ℂ)) →
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ z, f z = Q z * ∏ a ∈ s, (z - (a : ℂ)) ^ M := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f hf _; exact ⟨f, hf, fun z => by simp⟩
  | insert a s has ih =>
    intro f hf hord
    obtain ⟨q, hq, hqe⟩ := schwarz_factor_one (a : ℂ) M f hf (hord a (mem_insert_self _ _))
    have hfe : f = (fun z => z - (a : ℂ)) ^ M * q := by
      funext z; simp [hqe z]
    have hord' : ∀ b ∈ s, (M : ℕ∞) ≤ analyticOrderAt q (b : ℂ) := by
      intro b hb
      have hba : (b : ℂ) ≠ (a : ℂ) := by
        intro h; exact has (by have := Nat.cast_injective h; rwa [← this])
      have := hord b (mem_insert_of_mem hb)
      rw [hfe, analyticOrderAt_mul (by fun_prop) (hq.analyticAt _),
        analyticOrderAt_pow (by fun_prop), analyticOrderAt_id_sub_const_of_ne hba] at this
      simpa using this
    obtain ⟨Q, hQ, hQe⟩ := ih q hq hord'
    refine ⟨Q, hQ, fun z => ?_⟩
    rw [hqe z, hQe z, prod_insert has]; ring

/-- **L5.** The Schwarz-type bound for an entire function with zeros of order `M` at `0..h−1`. -/
theorem schwarz {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h M : ℕ)
    (hz : ∀ l < h, ∀ m < M, iteratedDeriv m g (l : ℂ) = 0) {R S : ℝ} (hR : (h : ℝ) < R)
    (hS : ∀ ζ : ℂ, ‖ζ‖ = R → ‖g ζ‖ ≤ S) {z : ℂ} (hzR : ‖z‖ ≤ R) :
    ‖g z‖ ≤ S * (∏ l ∈ range h, ‖z - (l : ℂ)‖ ^ M) / (R - h) ^ (h * M) := by
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hR0 : 0 < R := lt_of_le_of_lt hh0 hR
  have hRh : 0 < R - h := sub_pos.mpr hR
  obtain ⟨Q, hQ, hQe⟩ := schwarz_factor_finset M (range h) g hg (fun a ha => by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg.analyticAt _)]
    exact fun m hm => hz a (mem_range.mp ha) m hm)
  set D : ℝ := (R - h) ^ (h * M) with hD
  have hDpos : 0 < D := by positivity
  have hnormP : ∀ w : ℂ, ‖∏ a ∈ range h, (w - (a : ℂ)) ^ M‖ = ∏ a ∈ range h, ‖w - (a : ℂ)‖ ^ M := by
    intro w; simp [norm_prod, norm_pow]
  have hbd : ∀ ζ ∈ frontier (Metric.ball (0 : ℂ) R), ‖Q ζ‖ ≤ S / D := by
    intro ζ hζ
    rw [frontier_ball _ hR0.ne'] at hζ
    have hζn : ‖ζ‖ = R := by simpa using hζ
    have hlow : D ≤ ∏ a ∈ range h, ‖ζ - (a : ℂ)‖ ^ M := by
      have : ∏ a ∈ range h, (R - h) ^ M ≤ ∏ a ∈ range h, ‖ζ - (a : ℂ)‖ ^ M := by
        refine prod_le_prod₀ (fun _ _ => by positivity) (fun a ha => ?_)
        refine pow_le_pow_left₀ hRh.le ?_ M
        have h1 := norm_sub_norm_le ζ (a : ℂ)
        have h2 : ((a : ℕ) : ℝ) ≤ h := by exact_mod_cast (mem_range.mp ha).le
        simp only [Complex.norm_natCast] at h1
        linarith
      rw [prod_const, card_range, ← pow_mul, mul_comm M h] at this
      exact this
    have h1 : ‖g ζ‖ = ‖Q ζ‖ * ∏ a ∈ range h, ‖ζ - (a : ℂ)‖ ^ M := by
      rw [hQe ζ, norm_mul, hnormP]
    rw [le_div_iff₀ hDpos]
    calc ‖Q ζ‖ * D ≤ ‖Q ζ‖ * ∏ a ∈ range h, ‖ζ - (a : ℂ)‖ ^ M :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖g ζ‖ := h1.symm
      _ ≤ S := hS ζ hζn
  have hmax : ‖Q z‖ ≤ S / D := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hQ.diffContOnCl hbd ?_
    rw [closure_ball _ hR0.ne']
    simpa using hzR
  rw [hQe z, norm_mul, hnormP, mul_div_right_comm, mul_comm]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hmax (by positivity)

end Collatz.Gelfond
