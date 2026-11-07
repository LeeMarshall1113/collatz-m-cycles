import Collatz.MidRangeData

/-!
# Soundness of the middle-range check (Gelfond L11)

`midChain_sound`: if `midChain L segs = true` then for all `p` and all `K` with `L ≤ K < 10¹⁰⁰`,
`exp(−K/2⁸⁰) < |p log 2 − K log 3|`. Together with `midChain_ok`, this is the part of `EffMeasure`
between `10³⁶` and `10¹⁰⁰`, with no transcendence input. `effMeasure_of_100` glues it to the range
`K ≥ 10¹⁰⁰`.
-/

namespace Collatz

theorem exp_neg_le_two_pow (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    Real.exp (-x) ≤ 1 / 2 ^ n := by
  have h1 : Real.exp (-x) ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : (2 : ℝ) ^ n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) he n
  have h4 : Real.exp (-(n : ℝ)) = 1 / Real.exp n := by rw [Real.exp_neg]; simp
  rw [h4] at h1
  exact le_trans h1 (one_div_le_one_div_of_le (by positivity) h2)

/-- **Soundness of the middle-range chain.** -/
theorem midChain_sound : ∀ (segs : List FSeg) (L : ℕ), 1000 * 2 ^ 80 ≤ L →
    midChain L segs = true → ∀ p K : ℕ, L ≤ K → K < 10 ^ 100 →
      Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| := by
  intro segs
  induction segs with
  | nil =>
    intro L _ h p K hLK hK
    simp only [midChain, decide_eq_true_eq] at h
    omega
  | cons s rest ih =>
    intro L hL h p K hLK hK
    simp only [midChain] at h
    split_ifs at h with hs
    · exact ih L hL h p K hLK hK
    rw [Bool.and_eq_true] at h
    by_cases hKbd : s.b + s.d ≤ K
    · exact ih _ (by omega) h.2 p K hKbd hK
    push Not at hKbd
    have hseg := h.1
    simp only [midSegOK, decide_eq_true_eq] at hseg
    obtain ⟨hb, hd, hF, ha, hc, hL', hineq⟩ := hseg
    obtain ⟨mgq, hmg⟩ : ∃ q, q = min (deltaLo215 - (s.a : ℚ) / s.b) ((s.c : ℚ) / s.d - deltaHi215) :=
      ⟨_, rfl⟩
    rw [← hmg] at hineq
    have hmg1 : mgq ≤ deltaLo215 - (s.a : ℚ) / s.b := hmg ▸ min_le_left _ _
    have hmg2 : mgq ≤ (s.c : ℚ) / s.d - deltaHi215 := hmg ▸ min_le_right _ _
    have hK0 : 0 < K := by
      have : 0 < 1000 * 2 ^ 80 := by norm_num
      omega
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
    have hLR : (L : ℝ) ≤ K := by exact_mod_cast hLK
    have hL0R : (0 : ℝ) < L := by
      have : 0 < L := by
        have : 0 < 1000 * 2 ^ 80 := by norm_num
        omega
      exact_mod_cast this
    have hl2 := log_two_gt_q
    have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨hlo, hhi⟩ := logb_two_three_bounds215
    -- the real inequality
    have hineqR : (1 : ℝ) < 6931471803 / 10 ^ 10 * L * (mgq : ℝ) * 2 ^ 1000 := by
      have := (Rat.cast_lt (K := ℝ)).mpr hineq
      push_cast at this
      exact this
    have hmgpos : (0 : ℝ) < mgq := by
      by_contra hneg
      push Not at hneg
      have : 6931471803 / 10 ^ 10 * (L : ℝ) * (mgq : ℝ) * 2 ^ 1000 ≤ 0 := by
        have h1 : 6931471803 / 10 ^ 10 * (L : ℝ) * (mgq : ℝ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
        exact mul_nonpos_of_nonpos_of_nonneg h1 (by positivity)
      linarith
    -- exp bound
    have hx : (1000 : ℝ) ≤ (K : ℝ) / 2 ^ 80 := by
      rw [le_div_iff₀ (by positivity)]
      have : ((1000 * 2 ^ 80 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans hL' hLK
      push_cast at this
      linarith
    have hexp := exp_neg_le_two_pow 1000 (by exact_mod_cast hx)
    have h2pos : (0 : ℝ) < 2 ^ 1000 := by positivity
    have hlt : 1 / (2 : ℝ) ^ 1000 < 6931471803 / 10 ^ 10 * L * (mgq : ℝ) := by
      rw [div_lt_iff₀ h2pos]
      linarith
    -- the lower bound `|Λ| ≥ 0.69 L mg`
    have hcore : (K : ℝ) * mgq ≤ |(p : ℝ) - K * Real.logb 2 3| := by
      have hcases : (s.c : ℚ) / s.d ≤ (p : ℚ) / K ∨ (p : ℚ) / K ≤ (s.a : ℚ) / s.b := by
        by_contra hcon
        push Not at hcon
        have := farey_den_bound_div hK0 hb hd hF hcon.2 hcon.1
        omega
      rcases hcases with hc1 | hc1
      · have hc1R : (s.c : ℝ) / s.d ≤ (p : ℝ) / K := by
          have := (Rat.cast_le (K := ℝ)).mpr hc1
          push_cast at this
          exact this
        have hpK : (K : ℝ) * ((s.c : ℝ) / s.d) ≤ p := by
          rwa [le_div_iff₀ hKR, mul_comm] at hc1R
        have hm2 : (mgq : ℝ) ≤ (s.c : ℝ) / s.d - deltaHi215 := by exact_mod_cast hmg2
        have h1 : (K : ℝ) * mgq ≤ K * ((s.c : ℝ) / s.d - Real.logb 2 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hKR.le
        have h2 : (K : ℝ) * mgq ≤ (p : ℝ) - K * Real.logb 2 3 := by nlinarith
        exact le_trans h2 (le_abs_self _)
      · have hc1R : (p : ℝ) / K ≤ (s.a : ℝ) / s.b := by
          have := (Rat.cast_le (K := ℝ)).mpr hc1
          push_cast at this
          exact this
        have hpK : (p : ℝ) ≤ (K : ℝ) * ((s.a : ℝ) / s.b) := by
          rwa [div_le_iff₀ hKR, mul_comm] at hc1R
        have hm1 : (mgq : ℝ) ≤ deltaLo215 - (s.a : ℝ) / s.b := by exact_mod_cast hmg1
        have h1 : (K : ℝ) * mgq ≤ K * (Real.logb 2 3 - (s.a : ℝ) / s.b) :=
          mul_le_mul_of_nonneg_left (by linarith) hKR.le
        have h2 : (K : ℝ) * mgq ≤ K * Real.logb 2 3 - (p : ℝ) := by nlinarith
        have h3 : (K : ℝ) * Real.logb 2 3 - p = -((p : ℝ) - K * Real.logb 2 3) := by ring
        rw [h3] at h2
        exact le_trans h2 (neg_le_abs _)
    rw [lambda_eq, abs_mul, abs_of_pos hl2pos]
    have h5 : (L : ℝ) * mgq ≤ K * mgq := mul_le_mul_of_nonneg_right hLR hmgpos.le
    have h6 : 6931471803 / 10 ^ 10 * ((L : ℝ) * mgq) ≤ Real.log 2 * (K * mgq) := by
      have := mul_le_mul hl2.le h5 (by positivity) hl2pos.le
      exact this
    have h7 : Real.log 2 * (K * mgq) ≤ Real.log 2 * |(p : ℝ) - K * Real.logb 2 3| :=
      mul_le_mul_of_nonneg_left hcore hl2pos.le
    linarith

theorem midRange : ∀ p K : ℕ, 10 ^ 36 ≤ K → K < 10 ^ 100 →
    Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| :=
  fun p K hK hK' =>
    midChain_sound midSegs (10 ^ 36) (by norm_num) midChain_ok p K hK hK'

/-- `EffMeasure` follows from its `10¹⁰⁰`-threshold version. -/
theorem effMeasure_of_100
    (h100 : ∀ p K : ℕ, 10 ^ 100 ≤ K →
      Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3|) :
    EffMeasure := by
  intro p K hK
  by_cases h : K < 10 ^ 100
  · exact midRange p K hK h
  · exact h100 p K (not_lt.mp h)

end Collatz
