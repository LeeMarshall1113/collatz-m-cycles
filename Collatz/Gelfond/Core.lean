import Collatz.Gelfond.Basic
import Collatz.Gelfond.Analytic

/-!
# The Gelfond argument: Siegel's lemma, extrapolation, and the final Vandermonde step

`Setup` collects the parameters together with the exact numerical inequalities, `ExtIneq` and
`FinIneq`, that the analytic steps consume. `Params.lean` (L9) checks them for the concrete choice.
`gelfond_core` is the contradiction `|Λ| ≤ δ → False`.

* L2 `siegel` uses Mathlib's `Int.exists_ne_zero_int_vec_norm_le`.
* L6 `ext_step`: from `Ψ = 0` on `[0,h) × [0,M)` to `[0,2h) × [0,M)`. It uses L1, L3, L4, L5,
  Cauchy's estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) on circles of
  radius `1/2`, and integrality.
* L7 `final_step`: `F` is small on `|z| ≤ 1` (L4, L5 with `R = 20H`), so by Cauchy `F^{(m)}(0)` is
  small for `m < L²`. These values are `V c` with `V = (w_i^m)` a Vandermonde matrix, whose
  determinant is bounded below by L8. Since `c ≠ 0` is an integer vector, this is a contradiction.
-/

namespace Collatz.Gelfond

open Finset

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The coefficient bound from Siegel's lemma: `L² (3LK)^M 6^{L h₀}`. -/
noncomputable def siegelC (L M h0 K : ℕ) : ℝ := (L : ℝ) ^ 2 * (3 * L * K) ^ M * 6 ^ (L * h0)

/-- The bound for `|F^{(m)}(l)|` at nodes `l < h` once `Ψ` vanishes there:
`L² C · M · L δ (3L)^M 6^{L h}`. -/
noncomputable def epsAt (L M h0 K : ℕ) (δ : ℝ) (h : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * siegelC L M h0 K * M * L * δ * (3 * L) ^ M * 6 ^ (L * h)

/-- The Hermite growth factor `hM (2(R + h))^{hM}` of L4. -/
noncomputable def hermB (h M : ℕ) (R : ℝ) : ℝ := (h * M : ℝ) * (2 * (R + h)) ^ (h * M)

/-- The extrapolation inequality at `h` (outer circle `16h`, inner circles of radius `1/2`). -/
def ExtIneq (L M h0 K : ℕ) (δ : ℝ) (h : ℕ) : Prop :=
  (K : ℝ) ^ M * (M.factorial : ℝ) * 2 ^ M *
      (((L : ℝ) ^ 2 * siegelC L M h0 K * Real.exp (29 * L * h) +
            epsAt L M h0 K δ h * hermB h M (16 * h)) * (1 / 7) ^ (h * M) +
        epsAt L M h0 K δ h * hermB h M (2 * h + 1)) +
    (L : ℝ) ^ 2 * siegelC L M h0 K * M * L * δ * (3 * L * K) ^ M * 6 ^ (L * (2 * h)) <
    (69 / 100 : ℝ) ^ M

/-- The bound for `|F|` on `|z| ≤ 1` after extrapolation to `H` (outer circle `20H`). -/
noncomputable def finFmax (L M h0 K : ℕ) (δ : ℝ) (H : ℕ) : ℝ :=
  ((L : ℝ) ^ 2 * siegelC L M h0 K * Real.exp (36 * L * H) +
      epsAt L M h0 K δ H * hermB H M (20 * H)) * (1 / 19) ^ (H * M) +
    epsAt L M h0 K δ H * hermB H M 1

/-- The final inequality: `N · (N−1)! · (9L/5)^{N(N−1)/2} · 36^{L N(N−1)/2} · N! · Fmax < 1`,
with `N = L²`. -/
def FinIneq (L M h0 K : ℕ) (δ : ℝ) (H : ℕ) : Prop :=
  ((L ^ 2 : ℕ) : ℝ) * ((L ^ 2 - 1).factorial : ℝ) *
      (9 / 5 * (L : ℝ)) ^ (L ^ 2 * (L ^ 2 - 1) / 2) * (36 : ℝ) ^ (L * (L ^ 2 * (L ^ 2 - 1) / 2)) *
      ((L ^ 2).factorial : ℝ) * finFmax L M h0 K δ H < 1

/-- Parameters and the inequalities they must satisfy. -/
structure Setup where
  p : ℕ
  K : ℕ
  L : ℕ
  M : ℕ
  h0 : ℕ
  J : ℕ
  δ : ℝ
  hK : 1 ≤ K
  hpK : K ≤ p ∧ p ≤ 2 * K
  hL : 1 ≤ L
  hM : 1 ≤ M
  hh0 : 1 ≤ h0
  hsieg : 2 * h0 * M ≤ L * L
  hδ : 0 ≤ δ
  ext : ∀ j < J, ExtIneq L M h0 K δ (h0 * 2 ^ j)
  fin : FinIneq L M h0 K δ (h0 * 2 ^ J)

/-- **L2 (Siegel).** A nonzero integer vector `c` with `Ψ(l,m) = 0` for `l < h₀`, `m < M`. -/
theorem siegel {L M h0 p K : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (hh0 : 1 ≤ h0)
    (hS : 2 * h0 * M ≤ L * L) (hK : 1 ≤ K) (hpK : p ≤ 2 * K) :
    ∃ c : Idx L → ℤ, c ≠ 0 ∧ (∀ l < h0, ∀ m < M, Psi p K c l m = 0) ∧
      ∀ i, |(c i : ℝ)| ≤ siegelC L M h0 K := by
  classical
  let A : Matrix (Fin h0 × Fin M) (Idx L) ℤ := fun r i =>
    u p K i ^ (r.2 : ℕ) * (2 : ℤ) ^ ((i.1 : ℕ) * (r.1 : ℕ)) * (3 : ℤ) ^ ((i.2 : ℕ) * (r.1 : ℕ))
  have hcr : Fintype.card (Fin h0 × Fin M) = h0 * M := by simp
  have hcb : Fintype.card (Idx L) = L * L := by simp
  have hr0 : 0 < h0 * M := Nat.mul_pos hh0 hM
  have hn : Fintype.card (Fin h0 × Fin M) < Fintype.card (Idx L) := by
    rw [hcr, hcb]; nlinarith
  have hm : 0 < Fintype.card (Fin h0 × Fin M) := by rw [hcr]; exact hr0
  -- entry bound
  set B : ℝ := (3 * L * K : ℝ) ^ M * 6 ^ (L * h0) with hB
  have hLK : (1 : ℝ) ≤ 3 * L * K := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hLK) (one_le_pow₀ (by norm_num))
  have hnorm : ‖A‖ ≤ B := by
    rw [Matrix.norm_le_iff (by linarith)]
    intro r i
    rw [Int.norm_eq_abs]
    have hu0 : 0 ≤ u p K i := by unfold u; exact Int.natCast_nonneg _
    have hu : (u p K i : ℝ) ≤ 3 * L * K := by
      simp only [u]
      push_cast
      have h1 : ((i.1 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.1.isLt.le
      have h2 : ((i.2 : ℕ) : ℝ) ≤ L := by exact_mod_cast i.2.isLt.le
      have h3 : (p : ℝ) ≤ 2 * K := by exact_mod_cast hpK
      have h4 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      have h5 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      have h6 : (0 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h7 : (0 : ℝ) ≤ ((i.2 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul h1 (le_refl (K : ℝ)) h4 (Nat.cast_nonneg L),
        mul_le_mul h2 h3 h5 (Nat.cast_nonneg L)]
    have hl : (r.1 : ℕ) ≤ h0 := r.1.isLt.le
    have hmM : (r.2 : ℕ) ≤ M := r.2.isLt.le
    have e1 : (|A r i| : ℝ) = (u p K i : ℝ) ^ (r.2 : ℕ) * (2 : ℝ) ^ ((i.1 : ℕ) * (r.1 : ℕ)) *
        (3 : ℝ) ^ ((i.2 : ℕ) * (r.1 : ℕ)) := by
      have : ((|A r i| : ℤ) : ℝ) = |((A r i : ℤ) : ℝ)| := by push_cast; rfl
      rw [← Int.cast_abs] at *
      simp only [A]
      push_cast
      rw [abs_of_nonneg]
      positivity
    rw [e1]
    have hp1 : (u p K i : ℝ) ^ (r.2 : ℕ) ≤ (3 * L * K : ℝ) ^ M :=
      (pow_le_pow_left₀ (by exact_mod_cast hu0) hu _).trans
        (pow_le_pow_right₀ hLK hmM)
    have i1 : (i.1 : ℕ) * (r.1 : ℕ) ≤ L * h0 := Nat.mul_le_mul i.1.isLt.le hl
    have i2 : (i.2 : ℕ) * (r.1 : ℕ) ≤ L * h0 := Nat.mul_le_mul i.2.isLt.le hl
    have hp2 : (2 : ℝ) ^ ((i.1 : ℕ) * (r.1 : ℕ)) * (3 : ℝ) ^ ((i.2 : ℕ) * (r.1 : ℕ)) ≤
        6 ^ (L * h0) := by
      calc (2 : ℝ) ^ ((i.1 : ℕ) * (r.1 : ℕ)) * (3 : ℝ) ^ ((i.2 : ℕ) * (r.1 : ℕ))
          ≤ (2 : ℝ) ^ (L * h0) * (3 : ℝ) ^ (L * h0) :=
            mul_le_mul (pow_le_pow_right₀ (by norm_num) i1) (pow_le_pow_right₀ (by norm_num) i2)
              (by positivity) (by positivity)
        _ = 6 ^ (L * h0) := by rw [← mul_pow]; norm_num
    rw [hB, mul_assoc]
    exact mul_le_mul hp1 hp2 (by positivity) (by positivity)
  obtain ⟨c, hc0, hAc, hcn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm
  refine ⟨c, hc0, ?_, ?_⟩
  · intro l hl m hm'
    have := congrFun hAc (⟨l, hl⟩, ⟨m, hm'⟩)
    simp only [Matrix.mulVec, dotProduct, A, Pi.zero_apply] at this
    unfold Psi
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro i
    have hnb : (Fintype.card (Idx L) : ℝ) * max 1 ‖A‖ ≥ 1 := by
      rw [hcb]
      have : (1 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact one_le_mul_of_one_le_of_one_le this (le_max_left _ _)
    have hnbB : (Fintype.card (Idx L) : ℝ) * max 1 ‖A‖ ≤ (L : ℝ) ^ 2 * B := by
      rw [hcb]; push_cast
      rw [sq]
      exact mul_le_mul_of_nonneg_left (max_le hB1 hnorm) (by positivity)
    have hexp : ((Fintype.card (Fin h0 × Fin M) : ℕ) : ℝ) / ((Fintype.card (Idx L) : ℕ) - (Fintype.card (Fin h0 × Fin M) : ℕ)) ≤ 1 := by
      rw [hcr, hcb]
      have : ((2 * h0 * M : ℕ) : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast hS
      have h' : (0 : ℝ) < ((h0 * M : ℕ) : ℝ) := by exact_mod_cast hr0
      push_cast at this h' ⊢
      rw [div_le_one (by nlinarith)]
      nlinarith
    have h1 : ‖c‖ ≤ (L : ℝ) ^ 2 * B := by
      refine hcn.trans ?_
      refine (Real.rpow_le_rpow_of_exponent_le hnb hexp).trans ?_
      rw [Real.rpow_one]; exact hnbB
    have h2 : ‖c i‖ ≤ ‖c‖ := norm_le_pi_norm c i
    rw [Int.norm_eq_abs] at h2
    have : |(c i : ℝ)| ≤ (L : ℝ) ^ 2 * B := by
      exact h2.trans h1
    simpa [siegelC, hB, mul_assoc] using this

/-- **L6 (one extrapolation step).** -/
theorem ext_step (S : Setup) {c : Idx S.L → ℤ} (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K)
    (hΛ : |Lam S.p S.K| ≤ S.δ) {h : ℕ} (hh : S.h0 ≤ h) (hE : ExtIneq S.L S.M S.h0 S.K S.δ h)
    (hz : ∀ l < h, ∀ m < S.M, Psi S.p S.K c l m = 0) :
    ∀ l < 2 * h, ∀ m < S.M, Psi S.p S.K c l m = 0 := by
  sorry

/-- The extrapolation, iterated `J` times (proved from L6). -/
theorem extrapolate (S : Setup) {c : Idx S.L → ℤ}
    (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K) (hΛ : |Lam S.p S.K| ≤ S.δ)
    (h0z : ∀ l < S.h0, ∀ m < S.M, Psi S.p S.K c l m = 0) :
    ∀ j ≤ S.J, ∀ l < S.h0 * 2 ^ j, ∀ m < S.M, Psi S.p S.K c l m = 0 := by
  intro j
  induction j with
  | zero => intro _; simpa using h0z
  | succ j ih =>
    intro hj l hl m hm
    have hj' : j < S.J := by omega
    have hstep := ext_step S hc hΛ (h := S.h0 * 2 ^ j)
      (le_mul_of_one_le_right (Nat.zero_le _) (Nat.one_le_two_pow)) (S.ext j hj') (ih hj'.le)
    have e : S.h0 * 2 ^ (j + 1) = 2 * (S.h0 * 2 ^ j) := by ring
    rw [e] at hl
    exact hstep l hl m hm

/-- **L7 (final step).** -/
theorem final_step (S : Setup) {c : Idx S.L → ℤ} (hc0 : c ≠ 0)
    (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K) (hΛ : |Lam S.p S.K| ≤ S.δ)
    (hz : ∀ l < S.h0 * 2 ^ S.J, ∀ m < S.M, Psi S.p S.K c l m = 0) : False := by
  sorry

/-- **The Gelfond contradiction.** No `Setup` is compatible with `|Λ| ≤ δ`. -/
theorem gelfond_core (S : Setup) (hΛ : |Lam S.p S.K| ≤ S.δ) : False := by
  obtain ⟨c, hc0, h0z, hc⟩ := siegel S.hL S.hM S.hh0 S.hsieg S.hK S.hpK.2
  exact final_step S hc0 hc hΛ (extrapolate S hc hΛ h0z S.J le_rfl)

end Collatz.Gelfond
