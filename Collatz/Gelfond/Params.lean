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


/-! ### Bounds on the Siegel constant, `epsAt`, the Hermite factor -/

theorem x333 {b : ℕ} (hb : 333 ≤ b) : (333 : ℝ) ≤ b := by exact_mod_cast hb

theorem siegelC_nonneg (L M h0 K : ℕ) : 0 ≤ siegelC L M h0 K := by
  unfold siegelC; positivity

theorem xpow (x : ℝ) (hx : 333 ≤ x) :
    x * 333 ≤ x ^ 2 ∧ x ^ 2 * 333 ≤ x ^ 3 ∧ x ^ 3 * 333 ≤ x ^ 4 ∧ x ^ 4 * 333 ≤ x ^ 5 ∧
      x ^ 5 * 333 ≤ x ^ 6 := by
  have h0 : 0 ≤ x := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc x * 333 ≤ x * x := by gcongr
      _ = x ^ 2 := by ring
  · calc x ^ 2 * 333 ≤ x ^ 2 * x := by gcongr
      _ = x ^ 3 := by ring
  · calc x ^ 3 * 333 ≤ x ^ 3 * x := by gcongr
      _ = x ^ 4 := by ring
  · calc x ^ 4 * 333 ≤ x ^ 4 * x := by gcongr
      _ = x ^ 5 := by ring
  · calc x ^ 5 * 333 ≤ x ^ 5 * x := by gcongr
      _ = x ^ 6 := by ring

theorem siegelC_le {b K : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ)) :
    siegelC (400 * b) (19200 * b) (4 * b) K ≤ exp (27000 * (b : ℝ) ^ 2) := by
  have hx := x333 hb
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  unfold siegelC
  push_cast
  have h1 : (400 * (b : ℝ)) ^ 2 ≤ exp (((2 : ℕ) : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (by positivity) (cx_le_exp 400 b (by norm_num) (by norm_num) hx)
  have h3 : 3 * (400 * (b : ℝ)) * K ≤ exp ((b : ℝ) / 5 + b) := by
    have := cx_le_exp 1200 b (by norm_num) (by norm_num) hx
    exact mul_exp_le hK0 (by linarith) hK
  have h4 : (3 * (400 * (b : ℝ)) * K) ^ (19200 * b) ≤
      exp (((19200 * b : ℕ) : ℝ) * ((b : ℝ) / 5 + b)) := pow_le_exp (by positivity) h3
  have h5 : (6 : ℝ) ^ (400 * b * (4 * b)) ≤ exp (((400 * b * (4 * b) : ℕ) : ℝ) * 2) :=
    pow_le_exp (by norm_num) six_le_exp2
  have h6 := mul_exp_le (by positivity) (mul_exp_le (by positivity) h1 h4) h5
  refine le_trans h6 (Real.exp_le_exp.mpr ?_)
  push_cast
  nlinarith

theorem epsAt_eq (L M h0 K h : ℕ) (δ : ℝ) :
    epsAt L M h0 K δ h =
      ((L : ℝ) ^ 2 * siegelC L M h0 K * M * L * (3 * L) ^ M * 6 ^ (L * h)) * δ := by
  unfold epsAt; ring

theorem epsAt_le {b K : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ℕ) :
    epsAt (400 * b) (19200 * b) (4 * b) K δ h ≤
      exp (32000 * (b : ℝ) ^ 2 + 800 * b * h) * δ := by
  have hx := x333 hb
  have hC := siegelC_le hb hK
  have hCn := siegelC_nonneg (400 * b) (19200 * b) (4 * b) K
  rw [epsAt_eq]
  refine mul_le_mul_of_nonneg_right ?_ hδ
  push_cast
  have h1 : (400 * (b : ℝ)) ^ 2 ≤ exp (((2 : ℕ) : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (by positivity) (cx_le_exp 400 b (by norm_num) (by norm_num) hx)
  have h2 : 19200 * (b : ℝ) ≤ exp ((b : ℝ) / 5) := cx_le_exp 19200 b (by norm_num) (by norm_num) hx
  have h3 : 400 * (b : ℝ) ≤ exp ((b : ℝ) / 5) := cx_le_exp 400 b (by norm_num) (by norm_num) hx
  have h4 : (3 * (400 * (b : ℝ))) ^ (19200 * b) ≤ exp (((19200 * b : ℕ) : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (by positivity) (by
      have := cx_le_exp 1200 b (by norm_num) (by norm_num) hx
      linarith)
  have h5 : (6 : ℝ) ^ (400 * b * h) ≤ exp (((400 * b * h : ℕ) : ℝ) * 2) :=
    pow_le_exp (by norm_num) six_le_exp2
  have s1 := mul_exp_le hCn h1 hC
  have s2 := mul_exp_le (by positivity) s1 h2
  have s3 := mul_exp_le (by positivity) s2 h3
  have s4 := mul_exp_le (by positivity) s3 h4
  have s5 := mul_exp_le (by positivity) s4 h5
  refine le_trans s5 (Real.exp_le_exp.mpr ?_)
  push_cast
  nlinarith

theorem Q_le {b K : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ)) :
    (K : ℝ) ^ (19200 * b) * (((19200 * b).factorial : ℕ) : ℝ) * 2 ^ (19200 * b) ≤
      exp (24000 * (b : ℝ) ^ 2) := by
  have hx := x333 hb
  have hf : (((19200 * b).factorial : ℕ) : ℝ) ≤ (((19200 * b : ℕ)) : ℝ) ^ (19200 * b) := by
    exact_mod_cast Nat.factorial_le_pow (19200 * b)
  have hM : (((19200 * b : ℕ)) : ℝ) ≤ exp ((b : ℝ) / 5) := by
    push_cast; exact cx_le_exp 19200 b (by norm_num) (by norm_num) hx
  have h1 : (K : ℝ) ^ (19200 * b) ≤ exp (((19200 * b : ℕ) : ℝ) * (b : ℝ)) :=
    pow_le_exp (Nat.cast_nonneg K) hK
  have h2 : (((19200 * b : ℕ)) : ℝ) ^ (19200 * b) ≤ exp (((19200 * b : ℕ) : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (Nat.cast_nonneg _) hM
  have h3 : (2 : ℝ) ^ (19200 * b) ≤ exp (((19200 * b : ℕ) : ℝ) * 1) :=
    pow_le_exp (by norm_num) two_le_exp
  have s1 := mul_exp_le (Nat.cast_nonneg _) h1 (le_trans hf h2)
  have s2 := mul_exp_le (by positivity) s1 h3
  refine le_trans s2 (Real.exp_le_exp.mpr ?_)
  push_cast
  nlinarith

theorem hermB_le {b h : ℕ} (hb : 333 ≤ b) (hh1 : 1 ≤ h) (hh2 : (h : ℝ) ≤ 6 * 10 ^ 9 * (b : ℝ) ^ 4)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 20 * h) :
    hermB h (19200 * b) R ≤ exp (19200 * (b : ℝ) * h + 9600 * (b : ℝ) ^ 2 * h) := by
  have hx := x333 hb
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  unfold hermB
  push_cast
  have hb42 : 2 * (R + h) ≤ exp ((b : ℝ) / 2) := by
    have hc := cx_le_exp 252000000000 b (by norm_num) (by norm_num) hx
    have hx3 : (b : ℝ) ^ 3 ≤ exp (((3 : ℕ) : ℝ) * ((b : ℝ) / 10)) :=
      pow_le_exp (by positivity) (x_le_exp b hx)
    have hm := mul_exp_le (by positivity) hc hx3
    have hq : exp ((b : ℝ) / 5 + ((3 : ℕ) : ℝ) * ((b : ℝ) / 10)) = exp ((b : ℝ) / 2) := by
      congr 1; push_cast; ring
    rw [hq] at hm
    have : 2 * (R + h) ≤ 252000000000 * (b : ℝ) * (b : ℝ) ^ 3 := by nlinarith
    linarith
  have hpow : (2 * (R + h)) ^ (h * (19200 * b)) ≤
      exp (((h * (19200 * b) : ℕ) : ℝ) * ((b : ℝ) / 2)) :=
    pow_le_exp (by positivity) hb42
  have hpre : (h : ℝ) * (19200 * (b : ℝ)) ≤ exp ((h : ℝ) * (19200 * (b : ℝ))) := le_exp_self _
  have s := mul_exp_le (by positivity) hpre hpow
  refine le_trans s (Real.exp_le_exp.mpr (le_of_eq ?_))
  push_cast
  ring

theorem hermB_nonneg (h M : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ hermB h M R := by
  unfold hermB
  have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)

theorem eps_herm_le {b K h : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ)) (hh1 : 1 ≤ h)
    (hh2 : (h : ℝ) ≤ 6 * 10 ^ 9 * (b : ℝ) ^ 4) {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 20 * h)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    epsAt (400 * b) (19200 * b) (4 * b) K δ h * hermB h (19200 * b) R ≤
      exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ := by
  have hx := x333 hb
  have hxp := xpow b hx
  have e := epsAt_le hb hK hδ h
  have hh := hermB_le hb hh1 hh2 hR0 hR
  have hε : 0 ≤ epsAt (400 * b) (19200 * b) (4 * b) K δ h := by
    unfold epsAt siegelC; positivity
  have hB : 0 ≤ hermB h (19200 * b) R := hermB_nonneg _ _ hR0
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  calc epsAt (400 * b) (19200 * b) (4 * b) K δ h * hermB h (19200 * b) R
      ≤ (exp (32000 * (b : ℝ) ^ 2 + 800 * b * h) * δ) *
        exp (19200 * (b : ℝ) * h + 9600 * (b : ℝ) ^ 2 * h) :=
        mul_le_mul e hh hB (by positivity)
    _ = exp (32000 * (b : ℝ) ^ 2 + 800 * b * h + (19200 * (b : ℝ) * h + 9600 * (b : ℝ) ^ 2 * h))
          * δ := by
          rw [Real.exp_add (32000 * (b : ℝ) ^ 2 + 800 * b * h)
            (19200 * (b : ℝ) * h + 9600 * (b : ℝ) ^ 2 * h)]
          ring
    _ ≤ exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hδ
        have e1 : (b : ℝ) * h ≤ (b : ℝ) * (6 * 10 ^ 9 * (b : ℝ) ^ 4) := by gcongr
        have e2 : (b : ℝ) ^ 2 * h ≤ (b : ℝ) ^ 2 * (6 * 10 ^ 9 * (b : ℝ) ^ 4) := by gcongr
        obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
        nlinarith

theorem T3_le {b K h : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ))
    (hh2 : (h : ℝ) ≤ 6 * 10 ^ 9 * (b : ℝ) ^ 4) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((400 * b : ℕ) : ℝ) ^ 2 * siegelC (400 * b) (19200 * b) (4 * b) K * ((19200 * b : ℕ) : ℝ) *
        ((400 * b : ℕ) : ℝ) * δ * (3 * ((400 * b : ℕ) : ℝ) * K) ^ (19200 * b) *
        6 ^ (400 * b * (2 * h)) ≤ exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ := by
  have hx := x333 hb
  have hxp := xpow b hx
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hC := siegelC_le hb hK
  have hCn := siegelC_nonneg (400 * b) (19200 * b) (4 * b) K
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have key : ((400 * b : ℕ) : ℝ) ^ 2 * siegelC (400 * b) (19200 * b) (4 * b) K *
        ((19200 * b : ℕ) : ℝ) * ((400 * b : ℕ) : ℝ) * δ *
        (3 * ((400 * b : ℕ) : ℝ) * K) ^ (19200 * b) * 6 ^ (400 * b * (2 * h)) =
      (((400 * b : ℕ) : ℝ) ^ 2 * siegelC (400 * b) (19200 * b) (4 * b) K *
        ((19200 * b : ℕ) : ℝ) * ((400 * b : ℕ) : ℝ) *
        (3 * ((400 * b : ℕ) : ℝ) * K) ^ (19200 * b) * 6 ^ (400 * b * (2 * h))) * δ := by ring
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ hδ
  push_cast
  have h1 : (400 * (b : ℝ)) ^ 2 ≤ exp (((2 : ℕ) : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (by positivity) (cx_le_exp 400 b (by norm_num) (by norm_num) hx)
  have h2 : 19200 * (b : ℝ) ≤ exp ((b : ℝ) / 5) := cx_le_exp 19200 b (by norm_num) (by norm_num) hx
  have h3 : 400 * (b : ℝ) ≤ exp ((b : ℝ) / 5) := cx_le_exp 400 b (by norm_num) (by norm_num) hx
  have h4' : 3 * (400 * (b : ℝ)) * K ≤ exp ((b : ℝ) / 5 + b) := by
    have := cx_le_exp 1200 b (by norm_num) (by norm_num) hx
    exact mul_exp_le hK0 (by linarith) hK
  have h4 : (3 * (400 * (b : ℝ)) * K) ^ (19200 * b) ≤
      exp (((19200 * b : ℕ) : ℝ) * ((b : ℝ) / 5 + b)) := pow_le_exp (by positivity) h4'
  have h5 : (6 : ℝ) ^ (400 * b * (2 * h)) ≤ exp (((400 * b * (2 * h) : ℕ) : ℝ) * 2) :=
    pow_le_exp (by norm_num) six_le_exp2
  have s1 := mul_exp_le hCn h1 hC
  have s2 := mul_exp_le (by positivity) s1 h2
  have s3 := mul_exp_le (by positivity) s2 h3
  have s4 := mul_exp_le (by positivity) s3 h4
  have s5 := mul_exp_le (by positivity) s4 h5
  refine le_trans s5 (Real.exp_le_exp.mpr ?_)
  push_cast
  have e1 : (b : ℝ) * h ≤ (b : ℝ) * (6 * 10 ^ 9 * (b : ℝ) ^ 4) := by gcongr
  obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
  nlinarith


/-! ### The final-step prefactor and the abstract inequality shapes -/

theorem Pf_le {b L : ℕ} (hb : 333 ≤ b) (hL : L = 400 * b) :
    ((L ^ 2 : ℕ) : ℝ) * (((L ^ 2 - 1).factorial : ℕ) : ℝ) *
      (9 / 5 * (L : ℝ)) ^ (L ^ 2 * (L ^ 2 - 1) / 2) *
      (36 : ℝ) ^ (L * (L ^ 2 * (L ^ 2 - 1) / 2)) * (((L ^ 2).factorial : ℕ) : ℝ) ≤
      exp (42 * 10 ^ 12 * (b : ℝ) ^ 5) := by
  have hx := x333 hb
  have hxp := xpow b hx
  have hx0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLr : (L : ℝ) = 400 * (b : ℝ) := by rw [hL]; push_cast; ring
  obtain ⟨N, hN⟩ : ∃ N, N = L ^ 2 := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨e, he⟩ : ∃ e, e = N * (N - 1) / 2 := ⟨_, rfl⟩
  rw [← he]
  have hNr : (N : ℝ) = 160000 * (b : ℝ) ^ 2 := by rw [hN]; push_cast; rw [hLr]; ring
  have heN : e ≤ N * N := by
    rw [he]; exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul le_rfl (Nat.sub_le N 1))
  have heR : (e : ℝ) ≤ 25600000000 * (b : ℝ) ^ 4 := by
    have : (e : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast heN
    rw [hNr] at this; nlinarith
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hNe : (N : ℝ) ≤ exp (((2 : ℕ) : ℝ) * ((b : ℝ) / 5)) := by
    have h1 := pow_le_exp (n := 2) (y := 400 * (b : ℝ)) (by positivity)
      (cx_le_exp 400 b (by norm_num) (by norm_num) hx)
    have : (N : ℝ) = (400 * (b : ℝ)) ^ 2 := by rw [hN]; push_cast; rw [hLr]
    rw [this]; exact h1
  have hf2 : ((N.factorial : ℕ) : ℝ) ≤ exp ((N : ℝ) * (((2 : ℕ) : ℝ) * ((b : ℝ) / 5))) :=
    le_trans (by exact_mod_cast Nat.factorial_le_pow N) (pow_le_exp (Nat.cast_nonneg _) hNe)
  have hf1 : (((N - 1).factorial : ℕ) : ℝ) ≤ exp ((N : ℝ) * (((2 : ℕ) : ℝ) * ((b : ℝ) / 5))) :=
    le_trans (by exact_mod_cast Nat.factorial_le (Nat.sub_le N 1)) hf2
  have hp1 : (9 / 5 * (L : ℝ)) ^ e ≤ exp ((e : ℝ) * ((b : ℝ) / 5)) :=
    pow_le_exp (by positivity) (by
      rw [hLr]
      have := cx_le_exp 720 b (by norm_num) (by norm_num) hx
      linarith)
  have hp2 : (36 : ℝ) ^ (L * e) ≤ exp (((L * e : ℕ) : ℝ) * 4) :=
    pow_le_exp (by norm_num) thirtysix_le_exp4
  have s1 := mul_exp_le (Nat.cast_nonneg _) hNe hf1
  have s2 := mul_exp_le (by positivity) s1 hp1
  have s3 := mul_exp_le (by positivity) s2 hp2
  have s4 := mul_exp_le (Nat.cast_nonneg _) s3 hf2
  refine le_trans s4 (Real.exp_le_exp.mpr ?_)
  push_cast
  rw [hNr, hLr]
  have k1 : (b : ℝ) * e ≤ (b : ℝ) * (25600000000 * (b : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left heR hx0
  obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
  nlinarith

theorem ext_abs {Q A E eps B1 B2 w T3 P : ℝ} (hP : 0 < P)
    (h1 : Q * (A * E * w) ≤ P / 5) (h2 : Q * (eps * B1 * w) ≤ P / 5)
    (h3 : Q * (eps * B2) ≤ P / 5) (h4 : T3 ≤ P / 5) :
    Q * ((A * E + eps * B1) * w + eps * B2) + T3 < P := by
  have : Q * ((A * E + eps * B1) * w + eps * B2) =
      Q * (A * E * w) + Q * (eps * B1 * w) + Q * (eps * B2) := by ring
  rw [this]; linarith

theorem fin_abs {Pf A E eps B1 B2 w : ℝ}
    (h1 : Pf * (A * E * w) ≤ 1 / 5) (h2 : Pf * (eps * B1 * w) ≤ 1 / 5)
    (h3 : Pf * (eps * B2) ≤ 1 / 5) :
    Pf * ((A * E + eps * B1) * w + eps * B2) < 1 := by
  have : Pf * ((A * E + eps * B1) * w + eps * B2) =
      Pf * (A * E * w) + Pf * (eps * B1 * w) + Pf * (eps * B2) := by ring
  rw [this]; linarith

theorem small_of {T a : ℝ} {M : ℕ} (hT : T ≤ exp a) (ha : a ≤ -((M : ℝ) / 2) - 2) :
    T ≤ (69 / 100 : ℝ) ^ M / 5 := by
  calc T ≤ exp a := hT
    _ ≤ exp (-((M : ℝ) / 2) + -2) := Real.exp_le_exp.mpr (by linarith)
    _ = exp (-((M : ℝ) / 2)) * exp (-2) := Real.exp_add _ _
    _ ≤ (69 / 100 : ℝ) ^ M * (1 / 5) :=
        mul_le_mul (pow69_ge M) exp_neg_two_le (Real.exp_pos _).le (by positivity)
    _ = (69 / 100 : ℝ) ^ M / 5 := by ring

theorem small_one {T a : ℝ} (hT : T ≤ exp a) (ha : a ≤ -2) : T ≤ 1 / 5 :=
  le_trans hT (le_trans (Real.exp_le_exp.mpr ha) exp_neg_two_le)

theorem inv7_pow (n : ℕ) : (1 / 7 : ℝ) ^ n ≤ exp ((n : ℝ) * (-(3 / 2))) :=
  pow_le_exp (by norm_num) inv7_ge

theorem inv19_pow (n : ℕ) : (1 / 19 : ℝ) ^ n ≤ exp ((n : ℝ) * (-(5 / 2))) :=
  pow_le_exp (by norm_num) inv19_ge

theorem A_nonneg (b K : ℕ) :
    0 ≤ ((400 * b : ℕ) : ℝ) ^ 2 * siegelC (400 * b) (19200 * b) (4 * b) K :=
  mul_nonneg (by positivity) (siegelC_nonneg _ _ _ _)

theorem A_le {b K : ℕ} (hb : 333 ≤ b) (hK : (K : ℝ) ≤ exp (b : ℝ)) :
    ((400 * b : ℕ) : ℝ) ^ 2 * siegelC (400 * b) (19200 * b) (4 * b) K ≤
      exp (28000 * (b : ℝ) ^ 2) := by
  have hx := x333 hb
  have hC := siegelC_le hb hK
  have h1 : ((400 * b : ℕ) : ℝ) ^ 2 ≤ exp (((2 : ℕ) : ℝ) * ((b : ℝ) / 5)) := by
    calc ((400 * b : ℕ) : ℝ) ^ 2 = (400 * (b : ℝ)) ^ 2 := by push_cast; ring
      _ ≤ _ := pow_le_exp (by positivity) (cx_le_exp 400 b (by norm_num) (by norm_num) hx)
  have s := mul_exp_le (siegelC_nonneg _ _ _ _) h1 hC
  refine le_trans s (Real.exp_le_exp.mpr ?_)
  push_cast
  nlinarith

/-- bound `Q * T` for a delta term -/
theorem big_small {Q T δ : ℝ} {b M : ℕ} (hb : 333 ≤ b) (hM : M = 19200 * b) (hQ0 : 0 ≤ Q)
    (hT0 : 0 ≤ T) (hQ : Q ≤ exp (24000 * (b : ℝ) ^ 2))
    (hT : T ≤ exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ) (hδ : δ ≤ exp (-(10 ^ 15 * (b : ℝ) ^ 6))) :
    Q * T ≤ (69 / 100 : ℝ) ^ M / 5 := by
  have hx := x333 hb
  have hxp := xpow b hx
  have h1 : exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ ≤
      exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * exp (-(10 ^ 15 * (b : ℝ) ^ 6)) :=
    mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
  have h2 := mul_le_mul hQ (le_trans hT h1) hT0 (Real.exp_pos _).le
  simp only [← Real.exp_add] at h2
  refine small_of h2 ?_
  have hM' : (M : ℝ) = 19200 * (b : ℝ) := by rw [hM]; push_cast; ring
  rw [hM']
  obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
  nlinarith

theorem small_T {T δ : ℝ} {b M : ℕ} (hb : 333 ≤ b) (hM : M = 19200 * b) (hT0 : 0 ≤ T)
    (hT : T ≤ exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ) (hδ : δ ≤ exp (-(10 ^ 15 * (b : ℝ) ^ 6))) :
    T ≤ (69 / 100 : ℝ) ^ M / 5 := by
  have hx := x333 hb
  have hxp := xpow b hx
  have h1 : exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * δ ≤
      exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * exp (-(10 ^ 15 * (b : ℝ) ^ 6)) :=
    mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
  simp only [← Real.exp_add] at h1
  refine small_of (le_trans hT h1) ?_
  have hM' : (M : ℝ) = 19200 * (b : ℝ) := by rw [hM]; push_cast; ring
  rw [hM']
  obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
  nlinarith

/-! ### `ExtIneq` for every `h ∈ [4b, L⁴/10)` -/

theorem ext_ok {b K : ℕ} (hb : 333 ≤ b) (h2 : 2 ^ b ≤ 2 * K) (hK2 : K < 2 ^ b) {h : ℕ}
    (hh1 : 4 * b ≤ h) (hh2 : 10 * h < (400 * b) ^ 4) :
    ExtIneq (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) h := by
  have hx := x333 hb
  have hxp := xpow b hx
  have hK : (K : ℝ) ≤ exp (b : ℝ) := K_le_exp hK2
  have hδ0 : 0 ≤ exp (-((K : ℝ) / 2 ^ 80)) := (Real.exp_pos _).le
  have hδ : exp (-((K : ℝ) / 2 ^ 80)) ≤ exp (-(10 ^ 15 * (b : ℝ) ^ 6)) :=
    Real.exp_le_exp.mpr (neg_le_neg (D_ge hb h2))
  have hh1R : 4 * (b : ℝ) ≤ h := by exact_mod_cast hh1
  have hhR : (h : ℝ) ≤ 6 * 10 ^ 9 * (b : ℝ) ^ 4 := by
    have : (10 : ℝ) * h < (400 * (b : ℝ)) ^ 4 := by exact_mod_cast hh2
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) b) 4]
  have hh1' : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hxh : (b : ℝ) * (4 * b) ≤ (b : ℝ) * h :=
    mul_le_mul_of_nonneg_left hh1R (Nat.cast_nonneg b)
  have hQ := Q_le hb hK
  have hQ0 : 0 ≤ (K : ℝ) ^ (19200 * b) * (((19200 * b).factorial : ℕ) : ℝ) * 2 ^ (19200 * b) := by
    positivity
  unfold ExtIneq
  refine ext_abs (P := (69 / 100 : ℝ) ^ (19200 * b)) (by positivity) ?_ ?_ ?_ ?_
  · -- the non-delta main term
    have hA := A_le hb hK
    have hE : exp (29 * ((400 * b : ℕ) : ℝ) * h) ≤ exp (29 * ((400 * b : ℕ) : ℝ) * h) := le_rfl
    have hw := inv7_pow (h * (19200 * b))
    have s1 := mul_exp_le (by positivity) hA hE
    have s2 := mul_exp_le (by positivity) s1 hw
    have s3 := mul_exp_le (mul_nonneg (mul_nonneg (A_nonneg b K) (Real.exp_pos _).le)
      (by positivity)) hQ s2
    refine small_of s3 ?_
    push_cast
    obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
    nlinarith
  · -- T1''
    have hε := eps_herm_le hb hK hh1' hhR (R := 16 * h) (by positivity) (by linarith)
      (δ := exp (-((K : ℝ) / 2 ^ 80))) hδ0
    have hB0 := hermB_nonneg h (19200 * b) (R := 16 * (h : ℝ)) (by positivity)
    have hε0 : 0 ≤ epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) h := by
      unfold epsAt siegelC; positivity
    have hw1 : (1 / 7 : ℝ) ^ (h * (19200 * b)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hw0 : (0 : ℝ) ≤ (1 / 7 : ℝ) ^ (h * (19200 * b)) := by positivity
    have hT : epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) h *
        hermB h (19200 * b) (16 * h) * (1 / 7 : ℝ) ^ (h * (19200 * b)) ≤
        exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * exp (-((K : ℝ) / 2 ^ 80)) :=
      le_trans (mul_le_of_le_one_right (mul_nonneg hε0 hB0) hw1) hε
    exact big_small hb rfl hQ0 (mul_nonneg (mul_nonneg hε0 hB0) hw0) hQ hT hδ
  · -- T2
    have hε := eps_herm_le hb hK hh1' hhR (R := 2 * h + 1) (by positivity)
      (by have : (1 : ℝ) ≤ h := by exact_mod_cast hh1'
          linarith)
      (δ := exp (-((K : ℝ) / 2 ^ 80))) hδ0
    have hB0 := hermB_nonneg h (19200 * b) (R := 2 * (h : ℝ) + 1) (by positivity)
    have hε0 : 0 ≤ epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) h := by
      unfold epsAt siegelC; positivity
    exact big_small hb rfl hQ0 (mul_nonneg hε0 hB0) hQ hε hδ
  · -- T3
    exact small_T hb rfl (by unfold siegelC; positivity) (T3_le hb hK hhR hδ0) hδ

/-! ### `FinIneq` at `H ∈ [L⁴/10, L⁴/5)` -/

theorem fin_ok {b K : ℕ} (hb : 333 ≤ b) (h2 : 2 ^ b ≤ 2 * K) (hK2 : K < 2 ^ b) {H : ℕ}
    (hH1 : (400 * b) ^ 4 ≤ 10 * H) (hH2 : 5 * H < (400 * b) ^ 4) :
    FinIneq (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) H := by
  have hx := x333 hb
  have hxp := xpow b hx
  have hx0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hK : (K : ℝ) ≤ exp (b : ℝ) := K_le_exp hK2
  have hδ0 : 0 ≤ exp (-((K : ℝ) / 2 ^ 80)) := (Real.exp_pos _).le
  have hδ : exp (-((K : ℝ) / 2 ^ 80)) ≤ exp (-(10 ^ 15 * (b : ℝ) ^ 6)) :=
    Real.exp_le_exp.mpr (neg_le_neg (D_ge hb h2))
  have hH1R : (2.56 * 10 ^ 9) * (b : ℝ) ^ 4 ≤ H := by
    have : (400 * (b : ℝ)) ^ 4 ≤ 10 * H := by exact_mod_cast hH1
    nlinarith
  have hH2R : (H : ℝ) ≤ 6 * 10 ^ 9 * (b : ℝ) ^ 4 := by
    have : (5 : ℝ) * H < (400 * (b : ℝ)) ^ 4 := by exact_mod_cast hH2
    nlinarith [pow_nonneg hx0 4]
  have hH1' : 1 ≤ H := by
    have : 0 < (400 * b) ^ 4 := by positivity
    omega
  have hHr1 : (1 : ℝ) ≤ H := by exact_mod_cast hH1'
  have hHxb : (b : ℝ) * ((2.56 * 10 ^ 9) * (b : ℝ) ^ 4) ≤ (b : ℝ) * H :=
    mul_le_mul_of_nonneg_left hH1R hx0
  have hPf := Pf_le (b := b) (L := 400 * b) hb rfl
  unfold FinIneq finFmax
  refine fin_abs ?_ ?_ ?_
  · -- main term
    have hA := A_le hb hK
    have hE : exp (36 * ((400 * b : ℕ) : ℝ) * H) ≤ exp (36 * ((400 * b : ℕ) : ℝ) * H) := le_rfl
    have hw := inv19_pow (H * (19200 * b))
    have s1 := mul_exp_le (by positivity) hA hE
    have s2 := mul_exp_le (by positivity) s1 hw
    have s3 := mul_exp_le (mul_nonneg (mul_nonneg (A_nonneg b K) (Real.exp_pos _).le)
      (by positivity)) hPf s2
    refine small_one s3 ?_
    push_cast
    obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
    nlinarith
  · -- delta term with B(H, M, 20 H)
    have hε := eps_herm_le hb hK hH1' hH2R (R := 20 * H) (by positivity) le_rfl
      (δ := exp (-((K : ℝ) / 2 ^ 80))) hδ0
    have hB0 := hermB_nonneg H (19200 * b) (R := 20 * (H : ℝ)) (by positivity)
    have hε0 : 0 ≤ epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) H := by
      unfold epsAt siegelC; positivity
    have hw1 : (1 / 19 : ℝ) ^ (H * (19200 * b)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hT : epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) H *
        hermB H (19200 * b) (20 * H) * (1 / 19 : ℝ) ^ (H * (19200 * b)) ≤
        exp (8 * 10 ^ 13 * (b : ℝ) ^ 6) * exp (-((K : ℝ) / 2 ^ 80)) :=
      le_trans (mul_le_of_le_one_right (mul_nonneg hε0 hB0) hw1) hε
    have h1 := mul_le_mul hPf (le_trans hT (mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le))
      (mul_nonneg (mul_nonneg hε0 hB0) (by positivity)) (Real.exp_pos _).le
    simp only [← Real.exp_add] at h1
    refine small_one h1 ?_
    obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
    nlinarith
  · -- delta term with B(H, M, 1)
    have hε := eps_herm_le hb hK hH1' hH2R (R := 1) (by norm_num) (by linarith)
      (δ := exp (-((K : ℝ) / 2 ^ 80))) hδ0
    have hB0 := hermB_nonneg H (19200 * b) (R := 1) (by norm_num)
    have hε0 : 0 ≤ epsAt (400 * b) (19200 * b) (4 * b) K (exp (-((K : ℝ) / 2 ^ 80))) H := by
      unfold epsAt siegelC; positivity
    have h1 := mul_le_mul hPf (le_trans hε (mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le))
      (mul_nonneg hε0 hB0) (Real.exp_pos _).le
    simp only [← Real.exp_add] at h1
    refine small_one h1 ?_
    obtain ⟨p1, p2, p3, p4, p5⟩ := hxp
    nlinarith

/-! ### Choice of `J` and assembly of `Setup` -/

theorem exists_J (b : ℕ) (hb : 333 ≤ b) :
    ∃ J : ℕ, 0 < J ∧ (400 * b) ^ 4 ≤ 10 * (4 * b * 2 ^ J) ∧
      ∀ j < J, 10 * (4 * b * 2 ^ j) < (400 * b) ^ 4 := by
  classical
  have hex : ∃ J : ℕ, (400 * b) ^ 4 ≤ 10 * (4 * b * 2 ^ J) := by
    refine ⟨(400 * b) ^ 4, ?_⟩
    have h1 : (400 * b) ^ 4 < 2 ^ ((400 * b) ^ 4) := Nat.lt_two_pow_self
    have h2 : 2 ^ ((400 * b) ^ 4) ≤ 10 * (4 * b * 2 ^ ((400 * b) ^ 4)) := by
      have hb1 : 1 ≤ 10 * (4 * b) := by omega
      calc 2 ^ ((400 * b) ^ 4) = 1 * 2 ^ ((400 * b) ^ 4) := by ring
        _ ≤ (10 * (4 * b)) * 2 ^ ((400 * b) ^ 4) := Nat.mul_le_mul_right _ hb1
        _ = 10 * (4 * b * 2 ^ ((400 * b) ^ 4)) := by ring
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hcon
    have h0 : Nat.find hex = 0 := by omega
    have hs := Nat.find_spec hex
    rw [h0] at hs
    have h4 : 400 * b ≤ (400 * b) ^ 4 := Nat.le_self_pow (by norm_num) _
    simp at hs
    omega
  · intro j hj
    exact not_le.mp (Nat.find_min hex hj)

theorem setup_exists' {p K : ℕ} (hK : 10 ^ 100 ≤ K) (hpK : K ≤ p ∧ p ≤ 2 * K) :
    ∃ S : Setup, S.p = p ∧ S.K = K ∧ S.δ = Real.exp (-((K : ℝ) / 2 ^ 80)) := by
  obtain ⟨b, hb, h2, hK2⟩ := bitlen hK
  obtain ⟨J, hJ, hJ1, hJ2⟩ := exists_J b hb
  have hK1 : 1 ≤ K := by
    have : 0 < 10 ^ 100 := by norm_num
    omega
  refine ⟨{ p := p, K := K, L := 400 * b, M := 19200 * b, h0 := 4 * b, J := J,
            δ := Real.exp (-((K : ℝ) / 2 ^ 80)), hK := hK1, hpK := hpK, hL := by omega,
            hM := by omega, hh0 := by omega, hsieg := by nlinarith [Nat.zero_le (b * b)],
            hδ := (Real.exp_pos _).le, ext := ?_, fin := ?_ }, rfl, rfl, rfl⟩
  · intro j hj
    have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    refine ext_ok hb h2 hK2 (h := 4 * b * 2 ^ j) ?_ (hJ2 j hj)
    calc 4 * b = 4 * b * 1 := by ring
      _ ≤ 4 * b * 2 ^ j := Nat.mul_le_mul_left _ hpow
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    have h3 := hJ2 J' (by omega)
    refine fin_ok hb h2 hK2 (H := 4 * b * 2 ^ (J' + 1)) hJ1 ?_
    have : 5 * (4 * b * 2 ^ (J' + 1)) = 10 * (4 * b * 2 ^ J') := by ring
    rw [this]
    exact h3

end Params
end Collatz.Gelfond
