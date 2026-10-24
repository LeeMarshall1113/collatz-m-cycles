import Collatz.LogTwoThreeBounds

/-!
# A rational enclosure of `δ = log₂ 3` of width `10⁻⁸⁰`

Same method as `LogTwoThreeBounds.lean` (Mathlib's tail bound for the log series at `x = 1/2` and
`x = 1/3`), with `n = 285` and `n = 180`, so that both remainders are below `10⁻⁸⁵`. The 50-digit
enclosure is too coarse from `m = 111` on: the shape
`K = 29538024848568682064022389` has `P − K δ ≈ 2.39 · 10⁻²⁵` but `K (deltaHi − δ) ≈ 2.6 · 10⁻²⁵`.
Up to `m = 127` (Rhin ceiling `5.6 · 10²⁸`) about `10⁻⁵⁸` is needed.

Constants: `research/scripts/lean127` (exact `Fraction` evaluation of the two series bounds).
-/

namespace Collatz

/-- Lower end: `⌊10⁸⁰ · l₃/u₂⌋ / 10⁸⁰`. -/
def deltaLo80 : ℚ :=
  158496250072115618145373894394781650875981440769248106045575265454109822779435856 / 10 ^ 80

/-- Upper end: `⌈10⁸⁰ · u₃/l₂⌉ / 10⁸⁰`. -/
def deltaHi80 : ℚ :=
  158496250072115618145373894394781650875981440769248106045575265454109822779435857 / 10 ^ 80

theorem deltaHi80_sub_deltaLo80 : deltaHi80 - deltaLo80 = 1 / 10 ^ 80 := by decide +kernel

theorem deltaLo80_nonneg : (0 : ℚ) ≤ deltaLo80 := by decide +kernel

theorem deltaHi80_nonneg : (0 : ℚ) ≤ deltaHi80 := by decide +kernel

theorem log_two_bounds80 :
    ((logSum (1 / 2) 285 : ℚ) : ℝ) - 1 / 2 ^ 285 ≤ Real.log 2 ∧
      Real.log 2 ≤ ((logSum (1 / 2) 285 : ℚ) : ℝ) + 1 / 2 ^ 285 := by
  have h := abs_log_two_sub_logSum 285
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem log_three_bounds80 :
    ((logSum (1 / 2) 285 : ℚ) : ℝ) + ((logSum (1 / 3) 180 : ℚ) : ℝ) - 1 / 2 ^ 285 -
        1 / (2 * 3 ^ 180) ≤ Real.log 3 ∧
      Real.log 3 ≤ ((logSum (1 / 2) 285 : ℚ) : ℝ) + ((logSum (1 / 3) 180 : ℚ) : ℝ) + 1 / 2 ^ 285 +
        1 / (2 * 3 ^ 180) := by
  have h2 := log_two_bounds80
  have h3 := abs_log_three_sub_two_sub_logSum 180
  rw [abs_le] at h3
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

theorem deltaLo80_mul_lt :
    deltaLo80 * (logSum (1 / 2) 285 + 1 / 2 ^ 285) <
      logSum (1 / 2) 285 + logSum (1 / 3) 180 - 1 / 2 ^ 285 - 1 / (2 * 3 ^ 180) := by
  decide +kernel

theorem lt_deltaHi80_mul :
    logSum (1 / 2) 285 + logSum (1 / 3) 180 + 1 / 2 ^ 285 + 1 / (2 * 3 ^ 180) <
      deltaHi80 * (logSum (1 / 2) 285 - 1 / 2 ^ 285) := by
  decide +kernel

theorem deltaLo80_lt_logb : (deltaLo80 : ℝ) < Real.logb 2 3 := by
  rw [← Real.log_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hlog]
  have hu2 := log_two_bounds80.2
  have hl3 := log_three_bounds80.1
  have hkey : ((deltaLo80 * (logSum (1 / 2) 285 + 1 / 2 ^ 285) : ℚ) : ℝ) <
      ((logSum (1 / 2) 285 + logSum (1 / 3) 180 - 1 / 2 ^ 285 - 1 / (2 * 3 ^ 180) : ℚ) : ℝ) := by
    exact_mod_cast deltaLo80_mul_lt
  push_cast at hkey
  have hnn : (0 : ℝ) ≤ (deltaLo80 : ℝ) := by exact_mod_cast deltaLo80_nonneg
  have hm := mul_le_mul_of_nonneg_left hu2 hnn
  linarith

theorem logb_lt_deltaHi80 : Real.logb 2 3 < (deltaHi80 : ℝ) := by
  rw [← Real.log_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog]
  have hl2 := log_two_bounds80.1
  have hu3 := log_three_bounds80.2
  have hkey : ((logSum (1 / 2) 285 + logSum (1 / 3) 180 + 1 / 2 ^ 285 + 1 / (2 * 3 ^ 180) : ℚ) : ℝ) <
      ((deltaHi80 * (logSum (1 / 2) 285 - 1 / 2 ^ 285) : ℚ) : ℝ) := by
    exact_mod_cast lt_deltaHi80_mul
  push_cast at hkey
  have hnn : (0 : ℝ) ≤ (deltaHi80 : ℝ) := by exact_mod_cast deltaHi80_nonneg
  have hm := mul_le_mul_of_nonneg_left hl2 hnn
  linarith

/-- **The enclosure**: `deltaLo80 < log₂ 3 < deltaHi80`, width `10⁻⁸⁰`. -/
theorem logb_two_three_bounds80 :
    (deltaLo80 : ℝ) < Real.logb 2 3 ∧ Real.logb 2 3 < (deltaHi80 : ℝ) :=
  ⟨deltaLo80_lt_logb, logb_lt_deltaHi80⟩

end Collatz
