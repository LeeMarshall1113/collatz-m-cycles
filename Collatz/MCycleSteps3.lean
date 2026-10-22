import Collatz.MCycleSteps
import Collatz.ThreeRiseCheck

/-!
# The three-rise bound and three consecutive steps of the chain of minima

* `ThreeRiseBound N B`: the first three rises from an odd `n < 2^N` have total length at most `B`;
  `threeRiseBound_of_allTriples` derives it from the kernel-checked `ThreeRise.AllTriples N B`;
* `three_step_core` (Lemma 3S): `8 · 2^s (n''' + 1) ≤ 3^s (n + 8)`, `s = k + k' + k''`, from Alick's
  one- and two-block inequalities (`TwoRise.one_step_core`, `TwoRise.two_step_core`);
* `logb_three_step`: `x''' ≤ x + (δ − 1) s − 3 + 14/(n + 1)` for `x = log₂(n + 1)`.
-/

namespace Collatz

/-- **The three-rise bound below `2^N`.** -/
def ThreeRiseBound (N B : ℕ) : Prop :=
  ∀ n, n % 2 = 1 → n < 2 ^ N → orun n + orun (nextMin n) + orun (nextMin (nextMin n)) ≤ B

/-- **The three-rise bound from the kernel-checked arithmetic.** -/
theorem threeRiseBound_of_allTriples {N B : ℕ} (h : ThreeRise.AllTriples N B) :
    ThreeRiseBound N B := by
  intro n hn hN
  obtain ⟨a, ha, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', h2⟩ := block_eq hn'
  have hn'' : nextMin (nextMin n) % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a'', _, hna'', _⟩ := block_eq hn''
  have hk1 : 1 ≤ orun n := orun_pos hn
  have hle : 2 ^ orun n * a ≤ 2 ^ N := by rw [← hna]; omega
  have hkN : orun n ≤ N := by
    have h2 : 2 ^ orun n ≤ 2 ^ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  apply h (orun n) hk1 hkN a (erun n) (orun (nextMin n)) a' (erun (nextMin n))
    (orun (nextMin (nextMin n))) a'' ha hle (erun_pos n) (orun_pos hn') (erun_pos _) (orun_pos hn'')
  · rw [pow_add, mul_assoc, ← hna', h1]
    ring
  · rw [pow_add, mul_assoc, ← hna'', h2]
    ring

/-- **Lemma 3S**, three blocks: `8 · 2^{k+k'+k''} (n''' + 1) ≤ 3^{k+k'+k''} (n + 8)`. -/
theorem three_step_core {n n' n'' n''' k k' k'' a a' a'' l l' l'' : ℕ} (hn : n + 1 = 2 ^ k * a)
    (h1 : 3 ^ k * a = 2 ^ l * n' + 1) (hl : 1 ≤ l) (hn' : n' + 1 = 2 ^ k' * a')
    (h2 : 3 ^ k' * a' = 2 ^ l' * n'' + 1) (hl' : 1 ≤ l') (hn'' : n'' + 1 = 2 ^ k'' * a'')
    (h3 : 3 ^ k'' * a'' = 2 ^ l'' * n''' + 1) (hl'' : 1 ≤ l'') :
    8 * 2 ^ (k + k' + k'') * (n''' + 1) ≤ 3 ^ (k + k' + k'') * (n + 8) := by
  have s12 := TwoRise.two_step_core hn h1 hl hn' h2 hl'
  have s3 := TwoRise.one_step_core hn'' h3 hl''
  have hk : 2 ^ (k + k') ≤ 3 ^ (k + k') := Nat.pow_le_pow_left (by decide) _
  have hk'' : 2 ^ k'' ≤ 3 ^ k'' := Nat.pow_le_pow_left (by decide) _
  calc 8 * 2 ^ (k + k' + k'') * (n''' + 1)
      = 4 * 2 ^ (k + k') * (2 * 2 ^ k'' * (n''' + 1)) := by rw [pow_add]; ring
    _ ≤ 4 * 2 ^ (k + k') * (3 ^ k'' * (n'' + 1) + 2 ^ k'') := Nat.mul_le_mul_left _ s3
    _ = 3 ^ k'' * (4 * 2 ^ (k + k') * (n'' + 1)) + 4 * (2 ^ (k + k') * 2 ^ k'') := by ring
    _ ≤ 3 ^ k'' * (3 ^ (k + k') * (n + 4)) + 4 * (3 ^ (k + k') * 3 ^ k'') :=
        Nat.add_le_add (Nat.mul_le_mul_left _ s12) (Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hk''))
    _ = 3 ^ (k + k' + k'') * (n + 8) := by rw [pow_add]; ring

/-- **Three consecutive steps of the chain of minima**: with `x = log₂(n + 1)`,
`x''' ≤ x + (δ − 1)(k + k' + k'') − 3 + 14/(n + 1)` for the third next minimum. -/
theorem logb_three_step {n : ℕ} (hn : n % 2 = 1) :
    Real.logb 2 ((nextMin (nextMin (nextMin n)) : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 1) +
      (Real.logb 2 3 - 1) * ((orun n + orun (nextMin n) + orun (nextMin (nextMin n)) : ℕ) : ℝ) -
        3 + 14 / ((n : ℝ) + 1) := by
  obtain ⟨a, _, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', h2⟩ := block_eq hn'
  have hn'' : nextMin (nextMin n) % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a'', _, hna'', h3⟩ := block_eq hn''
  have hint := three_step_core hna h1 (erun_pos n) hna' h2 (erun_pos _) hna'' h3 (erun_pos _)
  obtain ⟨s, hs⟩ : ∃ s, s = orun n + orun (nextMin n) + orun (nextMin (nextMin n)) := ⟨_, rfl⟩
  rw [← hs] at hint ⊢
  have hR : (8 : ℝ) * 2 ^ s * ((nextMin (nextMin (nextMin n)) : ℝ) + 1) ≤
      (3 : ℝ) ^ s * ((n : ℝ) + 8) := by
    exact_mod_cast hint
  have hpos1 : (0 : ℝ) < (nextMin (nextMin (nextMin n)) : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 8 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  have e1 : Real.logb 2 ((8 : ℝ) * 2 ^ s * ((nextMin (nextMin (nextMin n)) : ℝ) + 1)) =
      3 + s + Real.logb 2 ((nextMin (nextMin (nextMin n)) : ℝ) + 1) := by
    rw [Real.logb_mul (by positivity) hpos1.ne', Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  have e2 : Real.logb 2 ((3 : ℝ) ^ s * ((n : ℝ) + 8)) =
      s * Real.logb 2 3 + Real.logb 2 ((n : ℝ) + 8) := by
    rw [Real.logb_mul (by positivity) hpos2.ne', Real.logb_pow]
  rw [e1, e2] at hlog
  have hq : Real.logb 2 ((n : ℝ) + 8) ≤ Real.logb 2 ((n : ℝ) + 1) + 14 / ((n : ℝ) + 1) := by
    have hn1' : (n : ℝ) + 1 ≠ 0 := hn1.ne'
    have e : (n : ℝ) + 8 = ((n : ℝ) + 1) * (1 + 7 / ((n : ℝ) + 1)) := by
      field_simp <;> ring
    rw [e, Real.logb_mul hn1.ne' (by positivity)]
    have := logb_one_add_le (show (0 : ℝ) ≤ 7 / ((n : ℝ) + 1) by positivity)
    have e3 : 2 * (7 / ((n : ℝ) + 1)) = 14 / ((n : ℝ) + 1) := by ring
    linarith
  linarith

end Collatz
