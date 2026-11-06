import Collatz.Gelfond.Core
import Collatz.Gelfond.Params
import Collatz.NoRhin

/-!
# `EffMeasure` at `10^100` from the Gelfond argument, and the m ≤ 111 theorem from 2^71 alone

* L9 `setup_exists` gives the concrete parameters, with `b` the bit length of `K` (`b ≥ 333`):
  `L = 400b`, `M = 48L = 19200b`, `h₀ = 4b`, `J` the least `j` with `10 h₀ 2^j ≥ L⁴`,
  `δ = exp(−K/2⁸⁰)`. The inequalities are proved in `Params.lean` with crude exponential bounds
  (the multiplier 48 replaces the plan's 24 of `PADE-PLAN.md` §3a, which needs sharper constants).
* L10 `effMeasure100` is proved here from L0, L9 and `gelfond_core`.
* L11 `noRhin_of_effMeasure100` is the m ≤ 111 chain with the ceiling threshold moved from `10^36`
  to `10^100`: 207 Farey segments and a 210-digit enclosure of `log₂ 3`.
-/

namespace Collatz.Gelfond

/-- The effective measure at `10^100`. -/
def EffMeasure100 : Prop :=
  ∀ p K : ℕ, 10 ^ 100 ≤ K →
    Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3|

/-- **L9.** The concrete parameters satisfy every inequality of `Setup`. -/
theorem setup_exists {p K : ℕ} (hK : 10 ^ 100 ≤ K) (hpK : K ≤ p ∧ p ≤ 2 * K) :
    ∃ S : Setup, S.p = p ∧ S.K = K ∧ S.δ = Real.exp (-((K : ℝ) / 2 ^ 80)) :=
  Params.setup_exists' hK hpK

/-- **L10.** The effective measure for `p log 2 − K log 3`, `K ≥ 10^100`. -/
theorem effMeasure100 : EffMeasure100 := by
  intro p K hK
  have hK1 : 1 ≤ K := le_trans (Nat.one_le_pow _ _ (by norm_num)) hK
  by_contra hcon
  push Not at hcon
  have hcon' : |Lam p K| ≤ Real.exp (-((K : ℝ) / 2 ^ 80)) := hcon
  by_cases hr : K ≤ p ∧ p ≤ 2 * K
  · obtain ⟨S, hp, hK', hδ⟩ := setup_exists hK hr
    apply gelfond_core S
    rw [hp, hK', hδ]
    exact hcon'
  · have h3 := one_third_le_abs_lam_of_range (p := p) hK1 (by omega)
    have hKR : (10 : ℝ) ^ 100 ≤ K := by exact_mod_cast hK
    have hexp : Real.exp (-((K : ℝ) / 2 ^ 80)) < 1 / 3 := by
      have h1 : Real.exp (-((K : ℝ) / 2 ^ 80)) ≤ Real.exp (-2) := by
        apply Real.exp_le_exp.mpr
        have h22 : (2 : ℝ) ≤ (K : ℝ) / 2 ^ 80 := by
          rw [le_div_iff₀ (by positivity)]
          have : (2 : ℝ) * 2 ^ 80 ≤ 10 ^ 100 := by norm_num
          linarith
        linarith
      have h2 : Real.exp (-2) < 1 / 3 := by
        rw [Real.exp_neg]
        have h3 := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
        rw [inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]
        norm_num
        linarith
      linarith
    linarith

/-- **L11.** The m ≤ 111 chain with the ceiling threshold at `10^100` (207 Farey segments, a
210-digit enclosure of `δ`). -/
theorem noRhin_of_effMeasure100 (hE : EffMeasure100)
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Collatz.Reaches Collatz.T n 1) :
    ∀ x p, 0 < x → 0 < p → Collatz.T^[p] x = x → x ≠ 1 → x ≠ 2 →
      112 ≤ Collatz.numLocalMin x p := by
  sorry

/-- **The goal of D90.** No Collatz m-cycle with `m ≤ 111`, assuming only Bařina's verification
bound `2^71`. -/
theorem main_statement_111_barina_only
    (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Collatz.Reaches Collatz.T n 1) :
    ∀ x p, 0 < x → 0 < p → Collatz.T^[p] x = x → x ≠ 1 → x ≠ 2 →
      112 ≤ Collatz.numLocalMin x p :=
  noRhin_of_effMeasure100 effMeasure100 hX

end Collatz.Gelfond
