import Collatz.MCycleWalk
import Collatz.MCycleSteps3

/-!
# The chain bound with one-, two- and three-step bounds, and the check for one `m`

The chain of `MCycleChain.lean` with a third candidate: besides `⌈δ⁺ Y_{t+2}⌉` and the double step
from `Y_{t+1}` (`chainNext`, two-rise grid `g2`), the triple step
`Y_t + ⌈0.584962501 · B · 2^S⌉ + 1 − 3 · 2^S` from `Y_t` with `ThreeRiseBound N B`, `(N, B)` in the
three-rise grid `g3` (`logb_three_step`). `chain3_sound`, `shape_false3` and `mOK3_sound` are
`chain_sound`, `shape_false` and `mOK_sound` with this chain; the bootstrap, the Rhin ceiling and
the Farey walk are Alick's, unchanged.
-/

namespace Collatz

open Finset

/-- The triple step `y ↦ y + (δ − 1) B − 3 + 2^{−S}` in units of `2^{−S}`. -/
def chainG3 (S B Y : ℕ) : ℕ := Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 - 3 * 2 ^ S

/-- `Y_{t+3}` from `Y_t = Ypp`, `Y_{t+1} = Yp`, `Y_{t+2} = Yc`. -/
def chainNext3 (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Ypp Yp Yc : ℕ) : ℕ :=
  match gridB S Ypp g3 with
  | none => chainNext S g2 Yp Yc
  | some B =>
    if 3 * 2 ^ S ≤ Ypp then min (chainNext S g2 Yp Yc) (chainG3 S B Ypp) else chainNext S g2 Yp Yc

/-- The chain as a sequence. -/
def chainSeq3 (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 : ℕ) : ℕ → ℕ
  | 0 => Y0
  | 1 => chainF Y0
  | 2 => chainNext S g2 Y0 (chainF Y0)
  | t + 3 => chainNext3 S g2 g3 (chainSeq3 S g2 g3 Y0 t) (chainSeq3 S g2 g3 Y0 (t + 1))
      (chainSeq3 S g2 g3 Y0 (t + 2))

theorem chainSeq3_zero (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 : ℕ) : chainSeq3 S g2 g3 Y0 0 = Y0 := by
  rw [chainSeq3]

theorem chainSeq3_one (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 : ℕ) :
    chainSeq3 S g2 g3 Y0 1 = chainF Y0 := by
  rw [chainSeq3]

theorem chainSeq3_two (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 : ℕ) :
    chainSeq3 S g2 g3 Y0 2 = chainNext S g2 Y0 (chainF Y0) := by
  rw [chainSeq3]

theorem chainSeq3_add_three (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 t : ℕ) :
    chainSeq3 S g2 g3 Y0 (t + 3) = chainNext3 S g2 g3 (chainSeq3 S g2 g3 Y0 t)
      (chainSeq3 S g2 g3 Y0 (t + 1)) (chainSeq3 S g2 g3 Y0 (t + 2)) := by
  rw [chainSeq3]

/-- The sum of the chain, by a loop: `chainSum3 f Y_t Y_{t+1} Y_{t+2} acc = acc + Σ_{i<f} Y_{t+i}`. -/
def chainSum3 (S : ℕ) (g2 g3 : List (ℕ × ℕ)) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | f + 1, Ypp, Yp, Yc, acc => chainSum3 S g2 g3 f Yp Yc (chainNext3 S g2 g3 Ypp Yp Yc) (acc + Ypp)

theorem chainSum3_eq (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 : ℕ) : ∀ f t acc,
    chainSum3 S g2 g3 f (chainSeq3 S g2 g3 Y0 t) (chainSeq3 S g2 g3 Y0 (t + 1))
        (chainSeq3 S g2 g3 Y0 (t + 2)) acc =
      acc + ∑ i ∈ range f, chainSeq3 S g2 g3 Y0 (t + i) := by
  intro f
  induction f with
  | zero => intro t acc; simp [chainSum3]
  | succ f ih =>
    intro t acc
    have e : chainNext3 S g2 g3 (chainSeq3 S g2 g3 Y0 t) (chainSeq3 S g2 g3 Y0 (t + 1))
        (chainSeq3 S g2 g3 Y0 (t + 2)) = chainSeq3 S g2 g3 Y0 (t + 1 + 2) :=
      (chainSeq3_add_three S g2 g3 Y0 t).symm
    have h := ih (t + 1) (acc + chainSeq3 S g2 g3 Y0 t)
    rw [show t + 1 + 1 = t + 2 from rfl] at h
    rw [chainSum3, e, h, sum_range_succ']
    have h2 : ∑ i ∈ range f, chainSeq3 S g2 g3 Y0 (t + 1 + i) =
        ∑ i ∈ range f, chainSeq3 S g2 g3 Y0 (t + (i + 1)) :=
      sum_congr rfl (fun i _ => by congr 1; omega)
    rw [h2, Nat.add_zero]
    ring

/-- `Σ_{t<m} Y_t` is the loop `chainSum3 m Y₀ Y₁ Y₂ 0`. -/
theorem chainSum3_start (S : ℕ) (g2 g3 : List (ℕ × ℕ)) (Y0 m : ℕ) :
    chainSum3 S g2 g3 m Y0 (chainF Y0) (chainNext S g2 Y0 (chainF Y0)) 0 =
      ∑ t ∈ range m, chainSeq3 S g2 g3 Y0 t := by
  have h := chainSum3_eq S g2 g3 Y0 m 0 0
  rw [chainSeq3_zero, show (0 : ℕ) + 1 = 1 from rfl, chainSeq3_one, show (0 : ℕ) + 2 = 2 from rfl,
    chainSeq3_two] at h
  rw [h, Nat.zero_add]
  exact sum_congr rfl (fun i _ => by rw [Nat.zero_add])

/-! ### One step of the chain -/

theorem chainF_step {S : ℕ} {δ x x' : ℝ} {Y : ℕ} (hδ : δ ≤ 1584962501 / 1000000000)
    (hx : 0 ≤ x) (hf : x' ≤ δ * x) (h : x ≤ (Y : ℝ) / 2 ^ S) : x' ≤ (chainF Y : ℝ) / 2 ^ S := by
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have h3 : δ * x ≤ (1584962501 / 1000000000) * ((Y : ℝ) / 2 ^ S) :=
    mul_le_mul hδ h hx (by norm_num)
  have h4 : (1584962501 / 1000000000 : ℝ) * ((Y : ℝ) / 2 ^ S) ≤ (chainF Y : ℝ) / 2 ^ S := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith [chainF_ge Y]) hS.le
  linarith

theorem chainGr_ge {S B Y r : ℕ} (hY : r * 2 ^ S ≤ Y) :
    (Y : ℝ) + (584962501 / 1000000000) * B * 2 ^ S + 1 - r * 2 ^ S ≤
      ((Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 - r * 2 ^ S : ℕ) : ℝ) := by
  have hc : 584962501 * B * 2 ^ S ≤
      (584962501 * B * 2 ^ S + 999999999) / 1000000000 * 1000000000 := by
    have := Nat.div_add_mod (584962501 * B * 2 ^ S + 999999999) 1000000000
    have := Nat.mod_lt (584962501 * B * 2 ^ S + 999999999) (show 0 < 1000000000 by norm_num)
    omega
  have hcR : ((584962501 * B * 2 ^ S : ℕ) : ℝ) ≤
      (((584962501 * B * 2 ^ S + 999999999) / 1000000000 * 1000000000 : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hcR
  have hle : r * 2 ^ S ≤ Y + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 := by omega
  rw [Nat.cast_sub hle]
  push_cast
  linarith

/-- The step `y ↦ y + (δ − 1) B − r + 2^{−S}` dominates. -/
theorem g_step {S B r : ℕ} {δ x0 x2 : ℝ} {Yp : ℕ} (hδ : δ ≤ 1584962501 / 1000000000)
    (hg : x2 ≤ x0 + (δ - 1) * B - r + 1 / 2 ^ S) (h0 : x0 ≤ (Yp : ℝ) / 2 ^ S)
    (hY : r * 2 ^ S ≤ Yp) :
    x2 ≤ ((Yp + (584962501 * B * 2 ^ S + 999999999) / 1000000000 + 1 - r * 2 ^ S : ℕ) : ℝ) /
      2 ^ S := by
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have h0' : x0 * 2 ^ S ≤ Yp := (le_div_iff₀ hS).mp h0
  have hG := chainGr_ge (B := B) hY
  rw [le_div_iff₀ hS]
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have h1 : (δ - 1) * B ≤ (584962501 / 1000000000) * B :=
    mul_le_mul_of_nonneg_right (by linarith) hB0
  have h1' := mul_le_mul_of_nonneg_right h1 hS.le
  have e : (1 : ℝ) / 2 ^ S * 2 ^ S = 1 := by field_simp
  have h2 : x2 * 2 ^ S ≤ (x0 + (δ - 1) * B - r + 1 / 2 ^ S) * 2 ^ S :=
    mul_le_mul_of_nonneg_right hg hS.le
  have h2' : (x0 + (δ - 1) * B - r + 1 / 2 ^ S) * 2 ^ S =
      x0 * 2 ^ S + (δ - 1) * B * 2 ^ S - r * 2 ^ S + 1 / 2 ^ S * 2 ^ S := by ring
  rw [h2', e] at h2
  linarith

/-- `chainNext` dominates (the inner step of Alick's `chain_sound`). -/
theorem chainNext_step {S : ℕ} {grid : List (ℕ × ℕ)} {δ x0 x1 x2 : ℝ} {Yp Yc : ℕ}
    (hδ : δ ≤ 1584962501 / 1000000000) (hx1 : 0 ≤ x1) (hf : x2 ≤ δ * x1)
    (hg : ∀ N B, (N, B) ∈ grid → x0 ≤ N → x2 ≤ x0 + (δ - 1) * B - 2 + 1 / 2 ^ S)
    (h0 : x0 ≤ (Yp : ℝ) / 2 ^ S) (h1 : x1 ≤ (Yc : ℝ) / 2 ^ S) :
    x2 ≤ (chainNext S grid Yp Yc : ℝ) / 2 ^ S := by
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have hf2 := chainF_step hδ hx1 hf h1
  unfold chainNext
  split
  · exact hf2
  · rename_i B hB
    split_ifs with hY
    · rw [Nat.cast_min, ← min_div_div_right hS.le]
      refine le_min hf2 ?_
      obtain ⟨N, hN, hYN⟩ := gridB_some hB
      have hYNR : (Yp : ℝ) ≤ N * 2 ^ S := by exact_mod_cast hYN
      have hxN : x0 ≤ N := by
        have := (le_div_iff₀ hS).mp h0
        exact le_of_mul_le_mul_right (by linarith) hS
      have hgt := hg N B hN hxN
      exact g_step (r := 2) hδ (by push_cast; linarith) h0 hY
    · exact hf2

/-- `chainNext3` dominates. -/
theorem chainNext3_step {S : ℕ} {g2 g3 : List (ℕ × ℕ)} {δ x0 x1 x2 x3 : ℝ} {Ypp Yp Yc : ℕ}
    (hδ : δ ≤ 1584962501 / 1000000000) (hx2 : 0 ≤ x2) (hf : x3 ≤ δ * x2)
    (hg : ∀ N B, (N, B) ∈ g2 → x1 ≤ N → x3 ≤ x1 + (δ - 1) * B - 2 + 1 / 2 ^ S)
    (hg3 : ∀ N B, (N, B) ∈ g3 → x0 ≤ N → x3 ≤ x0 + (δ - 1) * B - 3 + 1 / 2 ^ S)
    (h0 : x0 ≤ (Ypp : ℝ) / 2 ^ S) (h1 : x1 ≤ (Yp : ℝ) / 2 ^ S) (h2 : x2 ≤ (Yc : ℝ) / 2 ^ S) :
    x3 ≤ (chainNext3 S g2 g3 Ypp Yp Yc : ℝ) / 2 ^ S := by
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have hn := chainNext_step (grid := g2) hδ hx2 hf hg h1 h2
  unfold chainNext3
  split
  · exact hn
  · rename_i B hB
    split_ifs with hY
    · rw [Nat.cast_min, ← min_div_div_right hS.le]
      refine le_min hn ?_
      obtain ⟨N, hN, hYN⟩ := gridB_some hB
      have hYNR : (Ypp : ℝ) ≤ N * 2 ^ S := by exact_mod_cast hYN
      have hxN : x0 ≤ N := by
        have := (le_div_iff₀ hS).mp h0
        exact le_of_mul_le_mul_right (by linarith) hS
      have hgt := hg3 N B hN hxN
      exact g_step (r := 3) hδ (by push_cast; linarith) h0 hY
    · exact hn

/-- **The chain dominates.** -/
theorem chain3_sound {S : ℕ} {g2 g3 : List (ℕ × ℕ)} {Y0 : ℕ} {xs : ℕ → ℝ} {δ : ℝ}
    (hδ : δ ≤ 1584962501 / 1000000000) (hx0 : ∀ t, 0 ≤ xs t)
    (hf : ∀ t, xs (t + 1) ≤ δ * xs t)
    (hg : ∀ t N B, (N, B) ∈ g2 → xs t ≤ N →
      xs (t + 2) ≤ xs t + (δ - 1) * B - 2 + 1 / 2 ^ S)
    (hg3 : ∀ t N B, (N, B) ∈ g3 → xs t ≤ N →
      xs (t + 3) ≤ xs t + (δ - 1) * B - 3 + 1 / 2 ^ S)
    (h0 : xs 0 ≤ Y0 / 2 ^ S) : ∀ t, xs t ≤ chainSeq3 S g2 g3 Y0 t / 2 ^ S := by
  have key : ∀ t, xs t ≤ chainSeq3 S g2 g3 Y0 t / 2 ^ S ∧
      xs (t + 1) ≤ chainSeq3 S g2 g3 Y0 (t + 1) / 2 ^ S ∧
      xs (t + 2) ≤ chainSeq3 S g2 g3 Y0 (t + 2) / 2 ^ S := by
    intro t
    induction t with
    | zero =>
      have p0 : xs 0 ≤ chainSeq3 S g2 g3 Y0 0 / 2 ^ S := by rw [chainSeq3_zero]; exact h0
      have p1 : xs 1 ≤ chainSeq3 S g2 g3 Y0 1 / 2 ^ S := by
        rw [chainSeq3_one]; exact chainF_step hδ (hx0 0) (hf 0) h0
      refine ⟨p0, p1, ?_⟩
      show xs 2 ≤ chainSeq3 S g2 g3 Y0 2 / 2 ^ S
      rw [chainSeq3_two]
      rw [chainSeq3_one] at p1
      exact chainNext_step hδ (hx0 1) (hf 1) (fun N B hN hx => hg 0 N B hN hx) h0 p1
    | succ t ih =>
      obtain ⟨i0, i1, i2⟩ := ih
      refine ⟨i1, i2, ?_⟩
      show xs (t + 3) ≤ chainSeq3 S g2 g3 Y0 (t + 3) / 2 ^ S
      rw [chainSeq3_add_three]
      have hf' : xs (t + 3) ≤ δ * xs (t + 2) := hf (t + 2)
      have hg' : ∀ N B, (N, B) ∈ g2 → xs (t + 1) ≤ N →
          xs (t + 3) ≤ xs (t + 1) + (δ - 1) * B - 2 + 1 / 2 ^ S :=
        fun N B hN hx => hg (t + 1) N B hN hx
      exact chainNext3_step hδ (hx0 (t + 2)) hf' hg' (fun N B hN hx => hg3 t N B hN hx) i0 i1 i2
  exact fun t => (key t).1

/-! ### The certificate for one shape -/

/-- **The certificate check for one shape** with the three-term chain. -/
def shapeOK3 (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (c : ShapeCert) : Bool :=
  uOK m c && (decide (c.Ub ≤ 2 ^ 71 + 1) ||
    (decide (1 ≤ c.Q) && decide (c.Ub ^ c.Q ≤ 2 ^ c.Pe) &&
      decide (chainSum3 S g2 g3 m (c.Y0 S) (chainF (c.Y0 S)) (chainNext S g2 (c.Y0 S) (chainF (c.Y0 S)))
        0 < c.K * 2 ^ S)))

/-- **The exclusion of one shape** with two- and three-rise grids. -/
theorem shape_false3 {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hlow : ∀ j, 2 ^ 71 < T^[j] x) {m S : ℕ} {g2 g3 : List (ℕ × ℕ)}
    (hgrid2 : ∀ e ∈ g2, TwoRiseBound e.1 e.2) (hgrid3 : ∀ e ∈ g3, ThreeRiseBound e.1 e.2)
    (hS : S ≤ 60) (c : ShapeCert)
    (hm : numLocalMin x p = m) (hK : oddCount T x p = c.K) (hP : p = c.P)
    (hok : shapeOK3 m S g2 g3 c = true) : False := by
  obtain ⟨i, hmin, hleast⟩ := exists_least_rotation hx hp hcyc
  set y := T^[i] x with hy_def
  have hy : 0 < y := iterate_T_pos hx i
  have hcy : T^[p] y = y := cycle_rotate hcyc i
  have hmy : numLocalMin y p = m := by rw [hy_def, numLocalMin_rotate hp hcyc]; exact hm
  have hKy : oddCount T y p = c.K := by rw [hy_def, oddCount_rotate hcyc]; exact hK
  have hlowy : ∀ j, 2 ^ 71 < T^[j] y := fun j => by
    rw [hy_def, ← Function.iterate_add_apply]; exact hlow _
  have hleasty : ∀ j, y ≤ T^[j] y := fun j => by
    rw [hy_def, ← Function.iterate_add_apply]; exact hleast _
  simp only [shapeOK3, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hu, hrest⟩ := hok
  have hlt := least_lt_Ub hy hp hcy hleasty c hmy hKy hP hu
  have hltN : y < c.Ub := by exact_mod_cast hlt
  rcases hrest with hsmall | ⟨⟨hQ, hUbQ⟩, hsum⟩
  · have hy71 : 2 ^ 71 < y := by
      have := hlowy 0
      simpa using this
    omega
  · set xs : ℕ → ℝ := fun t => Real.logb 2 ((nextMin^[t] y : ℕ) + 1 : ℝ) with hxs
    have hδ1 := one_le_logb_two_three
    have hδ : Real.logb 2 3 ≤ 1584962501 / 1000000000 := by
      have h := logb_le_deltaUp
      have e : ((deltaUp : ℚ) : ℝ) = 1584962501 / 1000000000 := by norm_num [deltaUp]
      linarith
    have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 - 1 := by linarith
    have hx0 : ∀ t, 0 ≤ xs t := fun t =>
      Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (nextMin^[t] y)])
    have hodd : ∀ t, nextMin^[t] y % 2 = 1 := nextMin_iterate_odd hy hmin.1
    have hbig : ∀ t, 2 ^ 71 < nextMin^[t] y := fun t => by
      rw [← iterate_minPos]; exact hlowy _
    have hf : ∀ t, xs (t + 1) ≤ Real.logb 2 3 * xs t := by
      intro t
      simp only [hxs]
      rw [Function.iterate_succ_apply']
      exact (logb_nextMin_lt (nextMin_iterate_pos hy t) (hodd t)).le
    have hnt : ∀ t (N : ℕ), xs t ≤ N → nextMin^[t] y < 2 ^ N := by
      intro t N hxN
      have hpos : (0 : ℝ) < ((nextMin^[t] y : ℕ) : ℝ) + 1 := by positivity
      have h1 : ((nextMin^[t] y : ℕ) : ℝ) + 1 ≤ 2 ^ (N : ℝ) := by
        rw [← Real.logb_le_iff_le_rpow (by norm_num) hpos]
        exact hxN
      rw [Real.rpow_natCast] at h1
      have h2 : nextMin^[t] y + 1 ≤ 2 ^ N := by exact_mod_cast h1
      omega
    have hsmallS : ∀ t (C : ℝ), 0 ≤ C → C ≤ 1024 →
        C / (((nextMin^[t] y : ℕ) : ℝ) + 1) ≤ 1 / 2 ^ S := by
      intro t C hC0 hC
      have hbigR : ((2 ^ 71 : ℕ) : ℝ) < ((nextMin^[t] y : ℕ) : ℝ) := by exact_mod_cast hbig t
      push_cast at hbigR
      have hS2 : (2 : ℝ) ^ S ≤ 2 ^ 60 := pow_le_pow_right₀ (by norm_num) hS
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h60 : (2 : ℝ) ^ 60 * 1024 ≤ 2 ^ 71 := by norm_num
      have hSpos : (0 : ℝ) < 2 ^ S := by positivity
      have hm := mul_le_mul hC hS2 hSpos.le (by norm_num : (0 : ℝ) ≤ 1024)
      linarith
    have hg : ∀ t N B, (N, B) ∈ g2 → xs t ≤ N →
        xs (t + 2) ≤ xs t + (Real.logb 2 3 - 1) * B - 2 + 1 / 2 ^ S := by
      intro t N B hNB hxN
      have hkk := hgrid2 (N, B) hNB _ (hodd t) (hnt t N hxN)
      have h2 := logb_two_step (hodd t)
      have e2 : nextMin (nextMin (nextMin^[t] y)) = nextMin^[t + 2] y := by
        rw [show t + 2 = t + 1 + 1 from rfl, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
      rw [e2] at h2
      have hkR : ((orun (nextMin^[t] y) + orun (nextMin (nextMin^[t] y)) : ℕ) : ℝ) ≤ B := by
        exact_mod_cast hkk
      have h3 := mul_le_mul_of_nonneg_left hkR hδ0
      have h6 := hsmallS t 6 (by norm_num) (by norm_num)
      simp only [hxs]
      linarith
    have hg3 : ∀ t N B, (N, B) ∈ g3 → xs t ≤ N →
        xs (t + 3) ≤ xs t + (Real.logb 2 3 - 1) * B - 3 + 1 / 2 ^ S := by
      intro t N B hNB hxN
      have hkk := hgrid3 (N, B) hNB _ (hodd t) (hnt t N hxN)
      have h2 := logb_three_step (hodd t)
      have e3 : nextMin (nextMin (nextMin (nextMin^[t] y))) = nextMin^[t + 3] y := by
        rw [show t + 3 = t + 1 + 1 + 1 from rfl, Function.iterate_succ_apply',
          Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [e3] at h2
      have hkR : ((orun (nextMin^[t] y) + orun (nextMin (nextMin^[t] y)) +
          orun (nextMin (nextMin (nextMin^[t] y))) : ℕ) : ℝ) ≤ B := by
        exact_mod_cast hkk
      have h3 := mul_le_mul_of_nonneg_left hkR hδ0
      have h14 := hsmallS t 14 (by norm_num) (by norm_num)
      simp only [hxs]
      linarith
    have hY0 : xs 0 ≤ (c.Y0 S : ℝ) / 2 ^ S := by
      simp only [hxs, Function.iterate_zero, id_eq]
      have hy1 : ((y : ℕ) : ℝ) + 1 ≤ c.Ub := by
        have h' : y + 1 ≤ c.Ub := hltN
        exact_mod_cast h'
      have hQR : (0 : ℝ) < c.Q := by exact_mod_cast hQ
      have hUbpos : (0 : ℝ) < c.Ub := by linarith [Nat.cast_nonneg (α := ℝ) y]
      have hA : Real.logb 2 (((y : ℕ) : ℝ) + 1) ≤ Real.logb 2 c.Ub :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hy1
      have hB : (c.Q : ℝ) * Real.logb 2 c.Ub ≤ c.Pe := by
        have h1 : ((c.Ub ^ c.Q : ℕ) : ℝ) ≤ ((2 ^ c.Pe : ℕ) : ℝ) := by exact_mod_cast hUbQ
        push_cast at h1
        have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos hUbpos _) h1
        rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
        exact h2
      have hC : (c.Pe : ℝ) * 2 ^ S ≤ (c.Y0 S : ℝ) * c.Q := by
        have h : c.Pe * 2 ^ S ≤ c.Y0 S * c.Q := by
          unfold ShapeCert.Y0
          have := Nat.div_add_mod (c.Pe * 2 ^ S + c.Q - 1) c.Q
          have := Nat.mod_lt (c.Pe * 2 ^ S + c.Q - 1) (show 0 < c.Q by omega)
          have : (c.Pe * 2 ^ S + c.Q - 1) / c.Q * c.Q = c.Q * ((c.Pe * 2 ^ S + c.Q - 1) / c.Q) :=
            Nat.mul_comm _ _
          omega
        exact_mod_cast h
      have hS0 : (0 : ℝ) < 2 ^ S := by positivity
      rw [le_div_iff₀ hS0]
      have hD : Real.logb 2 (((y : ℕ) : ℝ) + 1) * c.Q ≤ c.Pe := by
        have := mul_le_mul_of_nonneg_right hA hQR.le
        linarith
      have hD' := mul_le_mul_of_nonneg_right hD hS0.le
      have hE : Real.logb 2 (((y : ℕ) : ℝ) + 1) * 2 ^ S * c.Q ≤ (c.Y0 S : ℝ) * c.Q := by
        have e : Real.logb 2 (((y : ℕ) : ℝ) + 1) * 2 ^ S * c.Q =
            Real.logb 2 (((y : ℕ) : ℝ) + 1) * c.Q * 2 ^ S := by ring
        rw [e]
        linarith
      exact le_of_mul_le_mul_right hE hQR
    have hdom := chain3_sound (g2 := g2) (g3 := g3) hδ hx0 hf hg hg3 hY0
    have hsumK := K_le_sum_logb hy hp hcy hmin
    rw [hKy, hmy] at hsumK
    have hsumY : ∑ t ∈ range m, xs t ≤
        ∑ t ∈ range m, (chainSeq3 S g2 g3 (c.Y0 S) t : ℝ) / 2 ^ S :=
      sum_le_sum (fun t _ => hdom t)
    rw [chainSum3_start S g2 g3 (c.Y0 S) m] at hsum
    have hsumR : (∑ t ∈ range m, (chainSeq3 S g2 g3 (c.Y0 S) t : ℝ)) < c.K * 2 ^ S := by
      have : ((∑ t ∈ range m, chainSeq3 S g2 g3 (c.Y0 S) t : ℕ) : ℝ) <
          ((c.K * 2 ^ S : ℕ) : ℝ) := by
        exact_mod_cast hsum
      push_cast at this
      exact this
    rw [← sum_div] at hsumY
    have hS0 : (0 : ℝ) < 2 ^ S := by positivity
    have : (∑ t ∈ range m, (chainSeq3 S g2 g3 (c.Y0 S) t : ℝ)) / 2 ^ S < c.K := by
      rw [div_lt_iff₀ hS0]; exact hsumR
    simp only [hxs] at hsumY
    linarith

/-! ### The check for one `m` -/

/-- Every listed shape has an accepted certificate (three-term chain). -/
def certsOK3 (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (certs : List ShapeCert)
    (shapes : List (ℕ × ℕ)) : Bool :=
  shapes.all (fun s => certs.any (fun c => c.K == s.1 && c.P == s.2 && shapeOK3 m S g2 g3 c))

theorem certsOK3_append (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (certs : List ShapeCert)
    (l₁ l₂ : List (ℕ × ℕ)) :
    certsOK3 m S g2 g3 certs (l₁ ++ l₂) =
      (certsOK3 m S g2 g3 certs l₁ && certsOK3 m S g2 g3 certs l₂) := by
  simp only [certsOK3, List.all_append]

/-- **The check for one `m`** (Alick's `mOK` with `certsOK3`). -/
def mOK3 (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (D : MData) : Bool :=
  chainOKX mX₀ m 1 D.boot D.Ks && rhinOK m D.Kceil D.V D.cexp D.kexp &&
    epsOKX mX₀ m D.Ks D.root &&
    decide (0 < D.rb ∧ 0 < D.rd ∧ D.rc * D.rb = D.ra * D.rd + 1 ∧
      (D.ra : ℚ) / D.rb ≤ deltaLo ∧ deltaHi + D.root.eps ≤ (D.rc : ℚ) / D.rd) &&
    D.stair.all (fun e => epsOKX mX₀ m e.1 e.2) &&
    !(D.shapes.contains ((0 : ℕ), (0 : ℕ))) && certsOK3 m S g2 g3 D.certs D.shapes

/-- **Soundness of the check for one `m`**: no nontrivial cycle with `m` local minima has all its
elements above `2⁷¹`, given `RhinBound` and the two- and three-rise bounds of the grids. -/
theorem mOK3_sound (hR : RhinBound) {m S : ℕ} {g2 g3 : List (ℕ × ℕ)}
    (hgrid2 : ∀ e ∈ g2, TwoRiseBound e.1 e.2) (hgrid3 : ∀ e ∈ g3, ThreeRiseBound e.1 e.2)
    (hS : S ≤ 60) {D : MData}
    (hok : mOK3 m S g2 g3 D = true) {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hm : numLocalMin x p = m) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    False := by
  simp only [mOK3, certsOK3, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hboot, hrhin⟩, hroot⟩, ⟨hrb, hrd, hF, hra, hrc⟩⟩, hstair⟩, hmark⟩, hcerts⟩ := hok
  have hpos := numLocalMin_pos hx hp hcyc
  have hm1 : 1 ≤ m := by rw [← hm]; exact hpos
  have hK1 : 1 ≤ oddCount T x p := oddCount_pos_of_numLocalMin_pos hpos
  have hX : 0 < mX₀ := by unfold mX₀; positivity
  have hlowX : ∀ j, mX₀ ≤ T^[j] x := fun j => by unfold mX₀; have := hlow j; omega
  have hKs := chainOKX_sound hx hp hcyc hm hm1 hX hlowX D.boot 1 D.Ks hK1 hboot
  have hKc := K_lt_of_rhinOK hR hx hp hcyc hx1 hx2 hm hrhin
  have hK0 : 0 < oddCount T x p := by omega
  have hr0 := ratio_lt_of_ratioIn hK0 (epsOKX_sound hx hp hcyc hm hm1 hX hlowX hroot hKs)
  have hhi : ∀ s ∈ D.pairs, s.1 ≤ oddCount T x p →
      (p : ℚ) / (oddCount T x p) < deltaHi + s.2 := by
    intro s hs hsK
    unfold MData.pairs at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
      exact (ratio_lt_of_ratioIn hK0 (epsOKX_sound hx hp hcyc hm hm1 hX hlowX
        (hstair e he) hsK)).2
    · rw [List.mem_singleton] at h
      subst h
      exact hr0.2
  have hw := walk_sound (stair := D.pairs) hKc hK0 hKs hr0.1 hhi D.fuel D.ra D.rb D.rc D.rd
    hrb hrd hF (lt_of_le_of_lt hra hr0.1) (lt_of_lt_of_le hr0.2 hrc)
  have hmem : (oddCount T x p, p) ∈ D.shapes := by
    rcases hw with h | h
    · exact h
    · exfalso
      have h' : D.shapes.contains ((0 : ℕ), (0 : ℕ)) = true := List.elem_eq_true_of_mem h
      rw [hmark] at h'
      exact Bool.false_ne_true h'
  obtain ⟨c, _, hc⟩ := List.any_eq_true.mp (hcerts _ hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hcK, hcP⟩, hshape⟩ := hc
  exact shape_false3 hx hp hcyc hlow hgrid2 hgrid3 hS c hm hcK.symm hcP.symm hshape

end Collatz
