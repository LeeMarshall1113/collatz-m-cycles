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

/-- **L4.** Hermite interpolation with a growth bound. -/
theorem hermite (h M : ℕ) (D : ℕ → ℕ → ℂ) {ε : ℝ} (hD : ∀ l < h, ∀ m < M, ‖D l m‖ ≤ ε)
    (hε : 0 ≤ ε) :
    ∃ P : Polynomial ℂ, (∀ l < h, ∀ m < M, (Polynomial.derivative^[m] P).eval (l : ℂ) = D l m) ∧
      ∀ z : ℂ, ‖P.eval z‖ ≤ ε * (h * M) * (2 * (‖z‖ + h)) ^ (h * M) := by
  sorry

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
