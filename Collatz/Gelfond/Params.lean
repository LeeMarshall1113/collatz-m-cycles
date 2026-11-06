import Collatz.Gelfond.Core

/-!
# L9 parameters: elementary lemmas for `setup_exists`

Concrete choice (see `PADE-PLAN.md` §3a; the multiplier `M = 48 L` replaces the plan's `24 L`,
because the crude constants used here need the extra room in the main extrapolation term):
`b` the bit length of `K`, `L = 400 b`, `M = 19200 b`, `h₀ = 4 b`, `δ = exp (-K / 2^80)`.
-/

set_option exponentiation.threshold 1000

namespace Collatz.Gelfond
namespace Params

open Real

/-- (a) The bit length of `K ≥ 10^100` is at least `333`. -/
theorem bitlen {K : ℕ} (hK : 10 ^ 100 ≤ K) :
    ∃ b : ℕ, 333 ≤ b ∧ 2 ^ b ≤ 2 * K ∧ K < 2 ^ b := by
  have hK0 : K ≠ 0 := by
    have : 0 < 10 ^ 100 := by norm_num
    omega
  refine ⟨Nat.log 2 K + 1, ?_, ?_, Nat.lt_pow_succ_log_self (by norm_num) K⟩
  · by_contra hcon
    have h1 : Nat.log 2 K + 1 ≤ 332 := by omega
    have h2 : K < 2 ^ 332 := lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) K)
      (Nat.pow_le_pow_right (by norm_num) h1)
    have h3 : (2 : ℕ) ^ 332 < 10 ^ 100 := by norm_num
    omega
  · have := Nat.pow_log_le_self 2 hK0
    rw [pow_succ]
    omega

/-! ### Elementary bounds for `exp` -/

theorem exp_one_gt' : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9

theorem exp_one_lt' : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)

theorem exp_nat' (n : ℕ) : exp (n : ℝ) = exp 1 ^ n := by
  have := Real.exp_nat_mul 1 n
  simpa using this

theorem two_le_exp : (2 : ℝ) ≤ exp 1 := by linarith [exp_one_gt']

theorem seven_le_exp2 : (7 : ℝ) ≤ exp 2 := by
  have h : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_one_gt']

theorem six_le_exp2 : (6 : ℝ) ≤ exp 2 := by linarith [seven_le_exp2]

theorem five_le_exp2 : (5 : ℝ) ≤ exp 2 := by linarith [seven_le_exp2]

theorem exp_neg_two_le : exp (-2) ≤ 1 / 5 := by
  rw [Real.exp_neg]
  have h := five_le_exp2
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem thirtysix_le_exp4 : (36 : ℝ) ≤ exp 4 := by
  have h : exp 4 = exp 2 * exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [seven_le_exp2]

theorem exp_three_half_le : exp (3 / 2) ≤ 7 := by
  have hy : exp (3 / 2) * exp (3 / 2) = exp 1 * exp 1 * exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  have h1 := exp_one_lt'
  have h0 := Real.exp_pos 1
  have hp := Real.exp_pos (3 / 2)
  have h3 : exp 1 * exp 1 * exp 1 ≤ 2.72 * 2.72 * 2.72 := by gcongr
  by_contra hcon
  push Not at hcon
  nlinarith

theorem exp_five_half_le : exp (5 / 2) ≤ 19 := by
  have hy : exp (5 / 2) * exp (5 / 2) = exp 1 ^ 5 := by
    rw [← Real.exp_add, ← exp_nat']; norm_num
  have h1 := exp_one_lt'
  have h0 := Real.exp_pos 1
  have hp := Real.exp_pos (5 / 2)
  have h3 : exp 1 ^ 5 ≤ 2.72 ^ 5 := by gcongr
  by_contra hcon
  push Not at hcon
  nlinarith

theorem inv7_ge : (1 / 7 : ℝ) ≤ exp (-(3 / 2)) := by
  rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (by norm_num) (Real.exp_pos _)]
  exact exp_three_half_le

theorem inv19_ge : (1 / 19 : ℝ) ≤ exp (-(5 / 2)) := by
  rw [Real.exp_neg, inv_eq_one_div, one_div_le_one_div (by norm_num) (Real.exp_pos _)]
  exact exp_five_half_le

theorem exp_neg_half_le : exp (-(1 / 2)) ≤ 69 / 100 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith

theorem pow69_ge (M : ℕ) : exp (-((M : ℝ) / 2)) ≤ (69 / 100 : ℝ) ^ M := by
  have h : exp (-((M : ℝ) / 2)) = exp (-(1 / 2)) ^ M := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h]
  exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_half_le M

theorem pow_le_exp {y a : ℝ} {n : ℕ} (hy : 0 ≤ y) (h : y ≤ exp a) :
    y ^ n ≤ exp ((n : ℝ) * a) := by
  rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ hy h n

theorem mul_exp_le {x y a c : ℝ} (hy : 0 ≤ y) (h1 : x ≤ exp a) (h2 : y ≤ exp c) :
    x * y ≤ exp (a + c) := by
  rw [Real.exp_add]; exact mul_le_mul h1 h2 hy (Real.exp_pos _).le

theorem le_exp_self (y : ℝ) : y ≤ exp y := by linarith [Real.add_one_le_exp y]

/-- the six-th power step -/
theorem six_step (b : ℕ) (hb : 333 ≤ b) : (b + 1) ^ 6 ≤ 2 * b ^ 6 := by
  have h : 9 * (b + 1) ≤ 10 * b := by omega
  have h2 : (9 * (b + 1)) ^ 6 ≤ (10 * b) ^ 6 := Nat.pow_le_pow_left h 6
  rw [mul_pow, mul_pow] at h2
  generalize (b + 1) ^ 6 = u at *
  generalize b ^ 6 = v at *
  norm_num at h2
  omega

/-- (c) the exact integer domination lemma (strengthened form). -/
theorem dom (b : ℕ) (hb : 333 ≤ b) : 10 ^ 15 * b ^ 6 * 2 ^ 81 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h6 := six_step n hn
    calc 10 ^ 15 * (n + 1) ^ 6 * 2 ^ 81 ≤ 10 ^ 15 * (2 * n ^ 6) * 2 ^ 81 := by gcongr
      _ = 2 * (10 ^ 15 * n ^ 6 * 2 ^ 81) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by ring

theorem D_ge {b K : ℕ} (hb : 333 ≤ b) (h2 : 2 ^ b ≤ 2 * K) :
    10 ^ 15 * (b : ℝ) ^ 6 ≤ (K : ℝ) / 2 ^ 80 := by
  have h := dom b hb
  have h' : (10 : ℝ) ^ 15 * (b : ℝ) ^ 6 * 2 ^ 81 ≤ 2 * (K : ℝ) := by
    exact_mod_cast le_trans h h2
  rw [le_div_iff₀ (by positivity)]
  norm_num at h' ⊢
  linarith

theorem x_le_exp (x : ℝ) (hx : 333 ≤ x) : x ≤ exp (x / 10) := by
  have h := Real.pow_div_factorial_le_exp (x / 10) (by positivity) 3
  have h6 : (((3 : ℕ).factorial : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  have h1 : x ^ 2 ≥ 6000 := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ x ^ 2 - 6000)]

theorem cx_le_exp (c x : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 10 ^ 12) (hx : 333 ≤ x) :
    c * x ≤ exp (x / 5) := by
  have h1 : c ≤ exp (x / 10) := by
    calc c ≤ 10 ^ 12 := hc
      _ ≤ (2.7 : ℝ) ^ 33 := by norm_num
      _ ≤ exp 1 ^ 33 := pow_le_pow_left₀ (by norm_num) exp_one_gt'.le 33
      _ = exp 33 := by rw [← exp_nat']; norm_num
      _ ≤ exp (x / 10) := Real.exp_le_exp.mpr (by linarith)
  calc c * x ≤ exp (x / 10) * exp (x / 10) :=
        mul_le_mul h1 (x_le_exp x hx) (by linarith) (Real.exp_pos _).le
    _ = exp (x / 5) := by rw [← Real.exp_add]; ring_nf

theorem K_le_exp {b K : ℕ} (hK : K < 2 ^ b) : (K : ℝ) ≤ exp (b : ℝ) := by
  have h1 : (K : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast hK.le
  calc (K : ℝ) ≤ (2 : ℝ) ^ b := h1
    _ ≤ exp 1 ^ b := pow_le_pow_left₀ (by norm_num) two_le_exp b
    _ = exp (b : ℝ) := by rw [exp_nat']

end Params
end Collatz.Gelfond
