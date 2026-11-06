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

/-- `n`-th iterated derivative of a polynomial function. -/
theorem iteratedDeriv_polyEval (P : Polynomial ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => P.eval z) = fun z => (Polynomial.derivative^[m] P).eval z := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun z : ℂ => P.eval z) = fun z => (Polynomial.derivative P).eval z := by
      funext z; simp
    rw [this, ih, Function.iterate_succ_apply]

/-- Input jets: `Ψ = 0` at `l < h`, `m < M` makes `|F^{(m)}(l)| ≤ epsAt`. -/
theorem jet_bound (S : Setup) {c : Idx S.L → ℤ}
    (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K) (hΛ : |Lam S.p S.K| ≤ S.δ) {h : ℕ}
    (hz : ∀ l < h, ∀ m < S.M, Psi S.p S.K c l m = 0) :
    ∀ l < h, ∀ m < S.M, ‖iteratedDeriv m (auxF c) (l : ℂ)‖ ≤ epsAt S.L S.M S.h0 S.K S.δ h := by
  intro l hl m hm
  have hap := approx S.hpK.2 c hc l m
  rw [hz l hl m hm] at hap
  have hK : (1 : ℝ) ≤ S.K := by exact_mod_cast S.hK
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast S.hL
  have hKm : (0 : ℝ) < (S.K : ℝ) ^ m := by positivity
  have hC : 0 ≤ siegelC S.L S.M S.h0 S.K := by unfold siegelC; positivity
  have hδ := S.hδ
  simp only [Int.cast_zero, mul_zero, sub_zero, norm_mul, norm_pow, Complex.norm_natCast] at hap
  have h3 : (3 * (S.L : ℝ) * S.K) ^ m = (3 * S.L) ^ m * S.K ^ m := by rw [mul_pow]
  rw [h3] at hap
  have key : ‖iteratedDeriv m (auxF c) (l : ℂ)‖ ≤
      (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K| * (3 * S.L) ^ m *
        6 ^ (S.L * l) := by
    refine le_of_mul_le_mul_left ?_ hKm
    calc _ ≤ _ := hap
      _ = _ := by ring
  refine key.trans ?_
  unfold epsAt
  have h3L : (1 : ℝ) ≤ 3 * S.L := by linarith
  have hmM : (m : ℝ) ≤ S.M := by exact_mod_cast hm.le
  have hlh : (6 : ℝ) ^ (S.L * l) ≤ (6 : ℝ) ^ (S.L * h) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hl.le)
  have hpm : (3 * (S.L : ℝ)) ^ m ≤ (3 * S.L) ^ S.M := pow_le_pow_right₀ h3L hm.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hM0 : (0 : ℝ) ≤ S.M := by linarith
  have hA : (0 : ℝ) ≤ |Lam S.p S.K| := abs_nonneg _
  have e1 : (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K| ≤
      (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * S.M * S.L * S.δ := by
    have : (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K ≥ 0 := by positivity
    gcongr
  have e2 : (3 * (S.L : ℝ)) ^ m * 6 ^ (S.L * l) ≤ (3 * S.L) ^ S.M * 6 ^ (S.L * h) :=
    mul_le_mul hpm hlh (by positivity) (by positivity)
  have e0 : 0 ≤ (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K| := by positivity
  calc _ = ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K|) *
        ((3 * (S.L : ℝ)) ^ m * 6 ^ (S.L * l)) := by ring
    _ ≤ ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * S.M * S.L * S.δ) *
        ((3 * (S.L : ℝ)) ^ S.M * 6 ^ (S.L * h)) := mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = _ := by ring

/-- The pointwise bound for `F` after interpolation and Schwarz. -/
theorem F_bound (S : Setup) {c : Idx S.L → ℤ}
    (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K) (hΛ : |Lam S.p S.K| ≤ S.δ) {h : ℕ}
    (hz : ∀ l < h, ∀ m < S.M, Psi S.p S.K c l m = 0) {R : ℝ} (hR : (h : ℝ) < R) {z : ℂ}
    (hzR : ‖z‖ ≤ R) :
    ‖auxF c z‖ ≤ ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (9 / 5 * S.L * R) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M R) *
        (∏ l ∈ range h, ‖z - (l : ℂ)‖ ^ S.M) / (R - h) ^ (h * S.M) +
      epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M ‖z‖ := by
  have hε : 0 ≤ epsAt S.L S.M S.h0 S.K S.δ h := by
    have := S.hδ
    unfold epsAt siegelC; positivity
  obtain ⟨P, hP1, hP2⟩ := hermite h S.M (fun l m => iteratedDeriv m (auxF c) (l : ℂ))
    (jet_bound S hc hΛ hz) hε
  have hgd : Differentiable ℂ (fun z => auxF c z - P.eval z) :=
    (differentiable_auxF c).sub P.differentiable
  have hg0 : ∀ l < h, ∀ m < S.M,
      iteratedDeriv m (fun z => auxF c z - P.eval z) (l : ℂ) = 0 := by
    intro l hl m hm
    rw [iteratedDeriv_fun_sub ((differentiable_auxF c).contDiff.contDiffAt)
      (P.differentiable.contDiff.contDiffAt), iteratedDeriv_polyEval]
    have : (Polynomial.derivative^[m] P).eval (l : ℂ) = iteratedDeriv m (auxF c) (l : ℂ) :=
      hP1 l hl m hm
    show iteratedDeriv m (auxF c) (l : ℂ) - (Polynomial.derivative^[m] P).eval (l : ℂ) = 0
    rw [this]; exact sub_self _
  have hS : ∀ ζ : ℂ, ‖ζ‖ = R → ‖auxF c ζ - P.eval ζ‖ ≤
      (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (9 / 5 * S.L * R) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M R := by
    intro ζ hζ
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have := norm_auxF_le c hc ζ
      rwa [hζ] at this
    · have := hP2 ζ
      rw [hζ] at this
      exact le_of_le_of_eq this (by unfold hermB; ring)
  have hsch : ‖auxF c z - P.eval z‖ ≤ _ := schwarz hgd h S.M hg0 hR hS hzR
  calc ‖auxF c z‖ = ‖(auxF c z - P.eval z) + P.eval z‖ := by rw [sub_add_cancel]
    _ ≤ ‖auxF c z - P.eval z‖ + ‖P.eval z‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hsch (le_of_le_of_eq (hP2 z) (by unfold hermB; ring))

/-- **L6 (one extrapolation step).** -/
theorem ext_step (S : Setup) {c : Idx S.L → ℤ} (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K)
    (hΛ : |Lam S.p S.K| ≤ S.δ) {h : ℕ} (hh : S.h0 ≤ h) (hE : ExtIneq S.L S.M S.h0 S.K S.δ h)
    (hz : ∀ l < h, ∀ m < S.M, Psi S.p S.K c l m = 0) :
    ∀ l < 2 * h, ∀ m < S.M, Psi S.p S.K c l m = 0 := by
  intro l' hl' m hm
  by_contra hne
  have hh1 : 1 ≤ h := le_trans S.hh0 hh
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hl'r : (l' : ℝ) + 1 ≤ 2 * h := by exact_mod_cast hl'
  have hK : (1 : ℝ) ≤ S.K := by exact_mod_cast S.hK
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast S.hL
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hC : 0 ≤ siegelC S.L S.M S.h0 S.K := by unfold siegelC; positivity
  have hε : 0 ≤ epsAt S.L S.M S.h0 S.K S.δ h := by
    have := S.hδ
    unfold epsAt siegelC; positivity
  have hδ := S.hδ
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K *
        Real.exp (29 * S.L * h) + epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (16 * h)) *
        (1 / 7) ^ (h * S.M) + epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (2 * h + 1) :=
    ⟨_, rfl⟩
  have hB16 : 0 ≤ hermB h S.M (16 * h) := by unfold hermB; positivity
  have hB2 : 0 ≤ hermB h S.M (2 * h + 1) := by unfold hermB; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hcirc : ∀ ζ : ℂ, ζ ∈ Metric.sphere (l' : ℂ) (1 / 2) → ‖auxF c ζ‖ ≤ B := by
    intro ζ hζ
    rw [mem_sphere_iff_norm] at hζ
    have hnζ : ‖ζ‖ ≤ 2 * h + 1 / 2 := by
      have e : ζ = (ζ - l') + l' := by ring
      have := norm_add_le (ζ - (l' : ℂ)) (l' : ℂ)
      rw [← e, hζ, Complex.norm_natCast] at this
      linarith
    have hR16 : (h : ℝ) < 16 * h := by linarith
    have hnζ16 : ‖ζ‖ ≤ 16 * (h : ℝ) := by linarith
    have hFb := F_bound S hc hΛ hz hR16 hnζ16
    have hprod : ∏ l ∈ range h, ‖ζ - (l : ℂ)‖ ^ S.M ≤ ((2 * (h : ℝ)) ^ S.M) ^ h := by
      have := Finset.prod_le_prod₀ (s :=range h) (f := fun l : ℕ => ‖ζ - (l : ℂ)‖ ^ S.M)
        (g := fun _ => (2 * (h : ℝ)) ^ S.M) (fun l _ => by positivity) (by
          intro l hl
          have hl' : l < h := Finset.mem_range.mp hl
          apply pow_le_pow_left₀ (norm_nonneg _)
          have e : ζ - (l : ℂ) = (ζ - l') + (((l' : ℝ) - l : ℝ) : ℂ) := by push_cast; ring
          have h1 : ‖ζ - (l : ℂ)‖ ≤ ‖ζ - (l' : ℂ)‖ + |(l' : ℝ) - l| := by
            calc _ = ‖(ζ - (l' : ℂ)) + (((l' : ℝ) - l : ℝ) : ℂ)‖ := by rw [e]
              _ ≤ _ := by
                refine (norm_add_le _ _).trans ?_
                rw [Complex.norm_real, Real.norm_eq_abs]
          have hlr : (l : ℝ) + 1 ≤ h := by exact_mod_cast hl'
          have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
          have h2 : |(l' : ℝ) - l| ≤ 2 * h - 1 := by
            rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg l' : (0 : ℝ) ≤ l')]
          rw [hζ] at h1
          linarith)
      rw [Finset.prod_const, Finset.card_range] at this
      exact this
    have hden : 0 < (16 * (h : ℝ) - h) := by linarith
    have hratio : (∏ l ∈ range h, ‖ζ - (l : ℂ)‖ ^ S.M) / (16 * (h : ℝ) - h) ^ (h * S.M) ≤
        (1 / 7) ^ (h * S.M) := by
      rw [div_le_iff₀ (pow_pos hden _)]
      calc _ ≤ ((2 * (h : ℝ)) ^ S.M) ^ h := hprod
        _ = (2 * (h : ℝ)) ^ (h * S.M) := by rw [← pow_mul, mul_comm S.M h]
        _ ≤ (1 / 7) ^ (h * S.M) * (16 * (h : ℝ) - h) ^ (h * S.M) := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          linarith
    have hX0 : 0 ≤ (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (9 / 5 * S.L * (16 * h)) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (16 * h) := by positivity
    have hXX : (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (9 / 5 * S.L * (16 * h)) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (16 * h) ≤
        (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (29 * S.L * h) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (16 * h) := by
      refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)) le_rfl
      have := mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ h)
      nlinarith
    have hmono : hermB h S.M ‖ζ‖ ≤ hermB h S.M (2 * h + 1) := by
      unfold hermB
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc ‖auxF c ζ‖ ≤ _ := hFb
      _ ≤ ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (29 * S.L * h) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (16 * h)) * (1 / 7) ^ (h * S.M) +
        epsAt S.L S.M S.h0 S.K S.δ h * hermB h S.M (2 * h + 1) := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hmono hε)
          rw [mul_div_assoc]
          exact (mul_le_mul_of_nonneg_left hratio hX0).trans
            (mul_le_mul_of_nonneg_right hXX (by positivity))
      _ = B := hBdef.symm
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (l' : ℂ))
    (R := 1 / 2) (C := B) (f := auxF c) m (by norm_num) (differentiable_auxF c).diffContOnCl hcirc
  have hder : ‖iteratedDeriv m (auxF c) (l' : ℂ)‖ ≤ (S.M.factorial : ℝ) * 2 ^ S.M * B := by
    refine hcau.trans ?_
    have e : (m.factorial : ℝ) * B / (1 / 2 : ℝ) ^ m = m.factorial * 2 ^ m * B := by
      rw [one_div, inv_pow, div_inv_eq_mul]; ring
    rw [e]
    have h1 : (m.factorial : ℝ) ≤ S.M.factorial := by exact_mod_cast Nat.factorial_le hm.le
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ S.M := pow_le_pow_right₀ (by norm_num) hm.le
    gcongr
  have happ := approx S.hpK.2 c hc l' m
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hPsi : (69 / 100 : ℝ) ^ S.M ≤ ‖((Real.log 2 : ℝ) : ℂ) ^ m * (Psi S.p S.K c l' m : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by norm_num))]
    have h1 : (1 : ℝ) ≤ ‖(Psi S.p S.K c l' m : ℂ)‖ := by
      rw [Complex.norm_intCast]
      have : (1 : ℤ) ≤ |Psi S.p S.K c l' m| := Int.one_le_abs hne
      exact_mod_cast this
    calc (69 / 100 : ℝ) ^ S.M ≤ (69 / 100) ^ m :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm.le
      _ ≤ (Real.log 2) ^ m := pow_le_pow_left₀ (by norm_num) hl2 m
      _ = (Real.log 2) ^ m * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (pow_nonneg (Real.log_pos (by norm_num)).le _)
  have htri : ‖((Real.log 2 : ℝ) : ℂ) ^ m * (Psi S.p S.K c l' m : ℂ)‖ ≤
      ‖(S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ)‖ +
        ‖(S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ) -
          ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi S.p S.K c l' m : ℂ)‖ := by
    calc _ = ‖(S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ) -
          ((S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ) -
            ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi S.p S.K c l' m : ℂ))‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have hA1 : ‖(S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ)‖ ≤
      (S.K : ℝ) ^ S.M * ((S.M.factorial : ℝ) * 2 ^ S.M * B) := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul (pow_le_pow_right₀ hK hm.le) hder (norm_nonneg _) (by positivity)
  have h3LK : (1 : ℝ) ≤ 3 * S.L * S.K := by nlinarith
  have hA2 : ‖(S.K : ℂ) ^ m * iteratedDeriv m (auxF c) (l' : ℂ) -
          ((Real.log 2 : ℝ) : ℂ) ^ m * (Psi S.p S.K c l' m : ℂ)‖ ≤
      (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * S.M * S.L * S.δ * (3 * S.L * S.K) ^ S.M *
        6 ^ (S.L * (2 * h)) := by
    refine happ.trans ?_
    have hmM : (m : ℝ) ≤ S.M := by exact_mod_cast hm.le
    have hpm : (3 * (S.L : ℝ) * S.K) ^ m ≤ (3 * S.L * S.K) ^ S.M := pow_le_pow_right₀ h3LK hm.le
    have hlh : (6 : ℝ) ^ (S.L * l') ≤ (6 : ℝ) ^ (S.L * (2 * h)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hl'.le)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hA : (0 : ℝ) ≤ |Lam S.p S.K| := abs_nonneg _
    have e1 : (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K| ≤
        (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * S.M * S.L * S.δ := by
      have : (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K ≥ 0 := by positivity
      gcongr
    have e2 : (3 * (S.L : ℝ) * S.K) ^ m * 6 ^ (S.L * l') ≤
        (3 * S.L * S.K) ^ S.M * 6 ^ (S.L * (2 * h)) :=
      mul_le_mul hpm hlh (by positivity) (by positivity)
    have e0 : 0 ≤ (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K| := by
      positivity
    calc _ = ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * m * S.L * |Lam S.p S.K|) *
          ((3 * (S.L : ℝ) * S.K) ^ m * 6 ^ (S.L * l')) := by ring
      _ ≤ ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * S.M * S.L * S.δ) *
          ((3 * (S.L : ℝ) * S.K) ^ S.M * 6 ^ (S.L * (2 * h))) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = _ := by ring
  have hE' := hE
  unfold ExtIneq at hE'
  rw [← hBdef] at hE'
  have hfin : (69 / 100 : ℝ) ^ S.M < (69 / 100 : ℝ) ^ S.M := by
    calc (69 / 100 : ℝ) ^ S.M ≤ _ := hPsi
      _ ≤ _ := htri
      _ ≤ _ := add_le_add hA1 hA2
      _ < _ := by
        convert hE' using 1
        ring
  exact lt_irrefl _ hfin

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

/-- Elementary: `2^n ≤ (n+1)!`. -/
theorem two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ (n + 1)]
    nlinarith [Nat.zero_le (n * (n + 1).factorial)]

/-- Linear-algebra-free Vandermonde step. -/
theorem vander_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (c w : ι → ℝ) {B ε : ℝ}
    (hB : ∀ i, |w i| ≤ B) (N : ℕ) (hT : ∀ r < N, |∑ i, c i * w i ^ r| ≤ ε) :
    ∀ s : Finset ι, ∀ r, r + s.card < N →
      |∑ i, c i * w i ^ r * ∏ a ∈ s, (w i - w a)| ≤ (1 + B) ^ s.card * ε := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    simpa using hT r (by simpa using hr)
  | insert a s has ih =>
    intro r hr
    rw [Finset.card_insert_of_notMem has] at hr ⊢
    have e : ∑ i, c i * w i ^ r * ∏ b ∈ insert a s, (w i - w b) =
        ∑ i, c i * w i ^ (r + 1) * ∏ b ∈ s, (w i - w b) -
          w a * ∑ i, c i * w i ^ r * ∏ b ∈ s, (w i - w b) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_insert has]; ring
    rw [e]
    have h1 := ih (r + 1) (by omega)
    have h2 := ih r (by omega)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a)
    calc _ ≤ |∑ i, c i * w i ^ (r + 1) * ∏ b ∈ s, (w i - w b)| +
          |w a * ∑ i, c i * w i ^ r * ∏ b ∈ s, (w i - w b)| := abs_sub _ _
      _ ≤ (1 + B) ^ s.card * ε + B * ((1 + B) ^ s.card * ε) := by
          rw [abs_mul]
          exact add_le_add h1 (mul_le_mul (hB a) h2 (abs_nonneg _) hB0)
      _ = (1 + B) ^ (s.card + 1) * ε := by ring

/-- The numerical inequality `FinIneq` implies the bound used with the Lagrange-type estimate. -/
theorem fin_arith (L : ℕ) (hL : 1 ≤ L) (Fm : ℝ) (hF : 0 ≤ Fm)
    (hfin : ((L ^ 2 : ℕ) : ℝ) * ((L ^ 2 - 1).factorial : ℝ) *
      (9 / 5 * (L : ℝ)) ^ (L ^ 2 * (L ^ 2 - 1) / 2) *
      (36 : ℝ) ^ (L * (L ^ 2 * (L ^ 2 - 1) / 2)) * ((L ^ 2).factorial : ℝ) * Fm < 1) :
    ((1 + 9 / 5 * (L : ℝ)) * 36 ^ L) ^ (L ^ 2 - 1) * (((L ^ 2).factorial : ℝ) * Fm) < 1 := by
  obtain ⟨n, hn⟩ : ∃ n, L ^ 2 = n + 1 :=
    ⟨L ^ 2 - 1, by have := pow_pos (show 0 < L from hL) 2; omega⟩
  rw [hn] at hfin ⊢
  simp only [Nat.add_sub_cancel] at hfin ⊢
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hB1 : (1 : ℝ) ≤ 9 / 5 * L := by linarith
  have hnE : n ≤ (n + 1) * n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rcases n with _ | n
    · simp
    · nlinarith
  have h2n : (2 : ℝ) ^ n ≤ ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
    have := two_pow_le_factorial n
    rw [Nat.factorial_succ] at this
    exact_mod_cast this
  have hP : ((1 + 9 / 5 * (L : ℝ)) * 36 ^ L) ^ n ≤
      ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * (9 / 5 * (L : ℝ)) ^ ((n + 1) * n / 2) *
        (36 : ℝ) ^ (L * ((n + 1) * n / 2)) := by
    rw [mul_pow, ← pow_mul]
    have a1 : (1 + 9 / 5 * (L : ℝ)) ^ n ≤ 2 ^ n * (9 / 5 * (L : ℝ)) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    have a2 : (9 / 5 * (L : ℝ)) ^ n ≤ (9 / 5 * (L : ℝ)) ^ ((n + 1) * n / 2) :=
      pow_le_pow_right₀ hB1 hnE
    have a3 : (36 : ℝ) ^ (L * n) ≤ (36 : ℝ) ^ (L * ((n + 1) * n / 2)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hnE)
    calc (1 + 9 / 5 * (L : ℝ)) ^ n * (36 : ℝ) ^ (L * n)
        ≤ (2 ^ n * (9 / 5 * (L : ℝ)) ^ n) * (36 : ℝ) ^ (L * n) :=
          mul_le_mul_of_nonneg_right a1 (by positivity)
      _ ≤ (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * (9 / 5 * (L : ℝ)) ^ ((n + 1) * n / 2)) *
          (36 : ℝ) ^ (L * ((n + 1) * n / 2)) := by
          refine mul_le_mul ?_ a3 (by positivity) (by positivity)
          exact mul_le_mul h2n a2 (by positivity) (by positivity)
  calc _ ≤ (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * (9 / 5 * (L : ℝ)) ^ ((n + 1) * n / 2) *
        (36 : ℝ) ^ (L * ((n + 1) * n / 2))) * (((n + 1).factorial : ℝ) * Fm) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
    _ < 1 := by
      refine lt_of_eq_of_lt ?_ hfin
      ring

/-- **L7 (final step).** -/
theorem final_step (S : Setup) {c : Idx S.L → ℤ} (hc0 : c ≠ 0)
    (hc : ∀ i, |(c i : ℝ)| ≤ siegelC S.L S.M S.h0 S.K) (hΛ : |Lam S.p S.K| ≤ S.δ)
    (hz : ∀ l < S.h0 * 2 ^ S.J, ∀ m < S.M, Psi S.p S.K c l m = 0) : False := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  obtain ⟨H, hH⟩ : ∃ H, H = S.h0 * 2 ^ S.J := ⟨_, rfl⟩
  rw [← hH] at hz
  have hfin := S.fin
  rw [← hH] at hfin
  have hH1 : 1 ≤ H := by
    rw [hH]; exact Nat.mul_pos S.hh0 (by positivity)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast S.hL
  have hK : (1 : ℝ) ≤ S.K := by exact_mod_cast S.hK
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hδ := S.hδ
  have hC : 0 ≤ siegelC S.L S.M S.h0 S.K := by unfold siegelC; positivity
  have hε : 0 ≤ epsAt S.L S.M S.h0 S.K S.δ H := by
    unfold epsAt siegelC; positivity
  obtain ⟨Fm, hFm⟩ : ∃ Fm, Fm = finFmax S.L S.M S.h0 S.K S.δ H := ⟨_, rfl⟩
  have hB20 : 0 ≤ hermB H S.M (20 * H) := by unfold hermB; positivity
  have hB1' : 0 ≤ hermB H S.M 1 := by unfold hermB; positivity
  have hFm0 : 0 ≤ Fm := by
    rw [hFm]; unfold finFmax; positivity
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖auxF c ζ‖ ≤ Fm := by
    intro ζ hζ
    have hR : (H : ℝ) < 20 * H := by linarith
    have hFb := F_bound S hc hΛ hz hR (z := ζ) (by rw [hζ]; linarith)
    have e36 : (9 / 5 * (S.L : ℝ) * (20 * H)) = 36 * S.L * H := by ring
    rw [e36, hζ] at hFb
    have hprod : ∏ l ∈ range H, ‖ζ - (l : ℂ)‖ ^ S.M ≤ ((H : ℝ) ^ S.M) ^ H := by
      have := Finset.prod_le_prod₀ (s := range H) (f := fun l : ℕ => ‖ζ - (l : ℂ)‖ ^ S.M)
        (g := fun _ => (H : ℝ) ^ S.M) (fun l _ => by positivity) (by
          intro l hl
          have hl' : l < H := Finset.mem_range.mp hl
          apply pow_le_pow_left₀ (norm_nonneg _)
          have h1 : ‖ζ - (l : ℂ)‖ ≤ ‖ζ‖ + ‖(l : ℂ)‖ := norm_sub_le _ _
          rw [hζ, Complex.norm_natCast] at h1
          have hlr : (l : ℝ) + 1 ≤ H := by exact_mod_cast hl'
          linarith)
      rw [Finset.prod_const, Finset.card_range] at this
      exact this
    have hden : 0 < (20 * (H : ℝ) - H) := by linarith
    have hratio : (∏ l ∈ range H, ‖ζ - (l : ℂ)‖ ^ S.M) / (20 * (H : ℝ) - H) ^ (H * S.M) ≤
        (1 / 19) ^ (H * S.M) := by
      rw [div_le_iff₀ (pow_pos hden _)]
      calc _ ≤ ((H : ℝ) ^ S.M) ^ H := hprod
        _ = (H : ℝ) ^ (H * S.M) := by rw [← pow_mul, mul_comm S.M H]
        _ ≤ (1 / 19) ^ (H * S.M) * (20 * (H : ℝ) - H) ^ (H * S.M) := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          linarith
    have hX0 : 0 ≤ (S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (36 * S.L * H) +
        epsAt S.L S.M S.h0 S.K S.δ H * hermB H S.M (20 * H) := by positivity
    calc ‖auxF c ζ‖ ≤ _ := hFb
      _ ≤ ((S.L : ℝ) ^ 2 * siegelC S.L S.M S.h0 S.K * Real.exp (36 * S.L * H) +
        epsAt S.L S.M S.h0 S.K S.δ H * hermB H S.M (20 * H)) * (1 / 19) ^ (H * S.M) +
        epsAt S.L S.M S.h0 S.K S.δ H * hermB H S.M 1 := by
          refine add_le_add ?_ le_rfl
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hratio hX0
      _ = Fm := by rw [hFm]; rfl
  have hT : ∀ m < S.L ^ 2, |∑ i : Idx S.L, (c i : ℝ) * w i ^ m| ≤
      ((S.L ^ 2).factorial : ℝ) * Fm := by
    intro m hm
    have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ))
      (R := 1) (C := Fm) (f := auxF c) m one_pos (differentiable_auxF c).diffContOnCl
      (fun z hz => hcirc z (by simpa using hz))
    have e : iteratedDeriv m (auxF c) 0 = ((∑ i : Idx S.L, (c i : ℝ) * w i ^ m : ℝ) : ℂ) := by
      rw [iteratedDeriv_auxF]; push_cast; simp
    rw [e, Complex.norm_real, Real.norm_eq_abs, one_pow, div_one] at hcau
    refine hcau.trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hm.le) hFm0
  have hB : ∀ i : Idx S.L, |w i| ≤ 9 / 5 * S.L := fun i => by
    rw [abs_of_nonneg (w_bounds i).1]; exact (w_bounds i).2
  have hcard : (Finset.univ.erase j).card = S.L ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, sq]
  have hNpos : 0 < S.L ^ 2 := pow_pos S.hL 2
  have hvb := vander_bound (fun i : Idx S.L => (c i : ℝ)) w hB (S.L ^ 2) hT
    (Finset.univ.erase j) 0 (by rw [hcard]; omega)
  have hlhs : ∑ i : Idx S.L, (c i : ℝ) * w i ^ 0 * ∏ a ∈ Finset.univ.erase j, (w i - w a) =
      (c j : ℝ) * ∏ a ∈ Finset.univ.erase j, (w j - w a) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩) (sub_self _),
        mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hlhs, hcard, abs_mul] at hvb
  have hsep : ((1 / 36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) ≤
      |∏ a ∈ Finset.univ.erase j, (w j - w a)| := by
    rw [Finset.abs_prod]
    have := Finset.prod_le_prod₀ (s := Finset.univ.erase j) (f := fun _ => (1 / 36 : ℝ) ^ S.L)
      (g := fun a => |w j - w a|) (fun _ _ => by positivity)
      (fun a ha => sep_w S.hL (Finset.ne_of_mem_erase ha).symm)
    rw [Finset.prod_const, hcard] at this
    exact this
  have hcj : |(c j : ℝ)| * ((1 / 36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) ≤
      (1 + 9 / 5 * (S.L : ℝ)) ^ (S.L ^ 2 - 1) * (((S.L ^ 2).factorial : ℝ) * Fm) :=
    (mul_le_mul_of_nonneg_left hsep (abs_nonneg _)).trans hvb
  have hone : ((1 / 36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) * ((36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) = 1 := by
    rw [← mul_pow, ← mul_pow]; norm_num
  have hlt : |(c j : ℝ)| < 1 := by
    have h36 : 0 ≤ ((36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hcj h36
    have hfa := fin_arith S.L S.hL Fm hFm0 (by rw [hFm]; exact hfin)
    calc |(c j : ℝ)| = |(c j : ℝ)| * (((1 / 36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) *
          ((36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1)) := by rw [hone, mul_one]
      _ = |(c j : ℝ)| * ((1 / 36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) *
          ((36 : ℝ) ^ S.L) ^ (S.L ^ 2 - 1) := by ring
      _ ≤ _ := h1
      _ = ((1 + 9 / 5 * (S.L : ℝ)) * 36 ^ S.L) ^ (S.L ^ 2 - 1) *
          (((S.L ^ 2).factorial : ℝ) * Fm) := by rw [mul_pow]; ring
      _ < 1 := hfa
  have : |c j| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at this
  exact hj (by omega)

/-- **The Gelfond contradiction.** No `Setup` is compatible with `|Λ| ≤ δ`. -/
theorem gelfond_core (S : Setup) (hΛ : |Lam S.p S.K| ≤ S.δ) : False := by
  obtain ⟨c, hc0, h0z, hc⟩ := siegel S.hL S.hM S.hh0 S.hsieg S.hK S.hpK.2
  exact final_step S hc0 hc hΛ (extrapolate S hc hΛ h0z S.J le_rfl)

end Collatz.Gelfond
