import Collatz.MCycleChain3
import Collatz.LogTwoThreeBounds80

/-!
# The three-term chain with the 80-digit enclosure of `log₂ 3` in the shape bound

From `m = 111` on, `uOK` with the 50-digit `deltaHi` rejects a shape whose `P − K δ` is below
`K (deltaHi − δ)` (`K = 29538024848568682064022389` at `m = 111`). `uOK80` is `uOK` with
`deltaHi80` (`LogTwoThreeBounds80.lean`); `uOKD = uOK || uOK80`. `shapeOK3D`, `shape_false3D`,
`certsOK3D`, `mOK3D` and `mOK3D_sound` are the `MCycleChain3` ones with `uOKD` (text copies; the
walk keeps the 50-digit enclosure, which suffices for it).
-/

namespace Collatz

open Finset

/-- The lower bound for `Λ − 1/(2^N − 1) − (m₂ − 1)/(2^M − 1)`. -/
def ShapeCert.room80 (c : ShapeCert) : ℚ :=
  ((c.P : ℚ) - c.K * deltaHi80) * (6931471803 / 10 ^ 10) - 1 / (2 ^ c.N - 1) -
    ((c.m₂ - 1 : ℕ) : ℚ) / (2 ^ c.M - 1)

/-- The rational side conditions of the bound `n₀ < U_b`. -/
def uOK80 (m : ℕ) (c : ShapeCert) : Bool :=
  decide (1 ≤ c.m₂ ∧ c.m₂ ≤ m ∧ 1 ≤ c.N ∧ 1 ≤ c.M ∧
    (c.N : ℚ) * m * geomQ deltaUp c.m₂ ≤ c.m₂ * c.K ∧
    (c.M : ℚ) * m * (1 + geomQ deltaUp (c.m₂ - 1)) ≤ c.m₂ * c.K ∧
    (c.K : ℚ) * deltaHi80 ≤ c.P ∧ 0 < c.room80 ∧ ((m - c.m₂ : ℕ) : ℚ) ≤ c.Ub * c.room80)

/-- **`n₀ < U_b`** for the least element `y` of a cycle of the given shape. -/
theorem least_lt_Ub80 {y p m : ℕ} (hy : 0 < y) (hp : 0 < p) (hcyc : T^[p] y = y)
    (hleast : ∀ j, y ≤ T^[j] y) (c : ShapeCert) (hm : numLocalMin y p = m)
    (hK : oddCount T y p = c.K) (hP : p = c.P) (hok : uOK80 m c = true) : (y : ℝ) < c.Ub := by
  simp only [uOK80, decide_eq_true_eq] at hok
  obtain ⟨hm1, hm2, hN1, hM1, hN, hM, hKP, hroom, hUb⟩ := hok
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlam := lambda_lt_two hy hp hcyc hm hm1 hm2 hyR (fun j => by exact_mod_cast hleast j)
    (Kp := c.K) (le_of_eq hK.symm) hN1 hM1 hN hM
  rw [hK, hP] at hlam
  -- `Λ > (p − K δ⁺) · 0.6931471803`
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : Real.log 3 = Real.logb 2 3 * Real.log 2 := by
    have := hlog2.ne'
    rw [Real.logb]
    field_simp
  have hδ := logb_lt_deltaHi80
  have hKP' : (c.K : ℝ) * (deltaHi80 : ℝ) ≤ c.P := by exact_mod_cast hKP
  have hl2 := log_two_gt'
  have hlam2 : ((c.P : ℝ) - c.K * (deltaHi80 : ℝ)) * (6931471803 / 10 ^ 10) ≤
      (c.P : ℝ) * Real.log 2 - (c.K : ℝ) * Real.log 3 := by
    rw [h3]
    have hK0 : (0 : ℝ) ≤ c.K := Nat.cast_nonneg _
    have a1 : (c.K : ℝ) * Real.logb 2 3 ≤ c.K * (deltaHi80 : ℝ) :=
      mul_le_mul_of_nonneg_left hδ.le hK0
    have a2 : ((c.P : ℝ) - c.K * (deltaHi80 : ℝ)) * (6931471803 / 10 ^ 10) ≤
        ((c.P : ℝ) - c.K * (deltaHi80 : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    nlinarith
  -- the room
  have hroomR : ((c.room80 : ℚ) : ℝ) = ((c.P : ℝ) - c.K * (deltaHi80 : ℝ)) * (6931471803 / 10 ^ 10) -
      1 / ((2 : ℝ) ^ c.N - 1) - ((c.m₂ - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ c.M - 1) := by
    simp only [ShapeCert.room80]
    push_cast <;> ring
  have hroomPos : (0 : ℝ) < ((c.room80 : ℚ) : ℝ) := by exact_mod_cast hroom
  have hUbR : ((m - c.m₂ : ℕ) : ℝ) ≤ (c.Ub : ℝ) * ((c.room80 : ℚ) : ℝ) := by exact_mod_cast hUb
  -- `(m − m₂)/y > room`
  have hmain : ((c.room80 : ℚ) : ℝ) < ((m - c.m₂ : ℕ) : ℝ) / y := by
    rw [hroomR]; linarith
  rw [lt_div_iff₀ hyR] at hmain
  by_contra hge
  push_neg at hge
  have : (c.Ub : ℝ) * ((c.room80 : ℚ) : ℝ) ≤ y * ((c.room80 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right hge hroomPos.le
  linarith

/-- The shape bound with either enclosure. -/
def uOKD (m : ℕ) (c : ShapeCert) : Bool := uOK m c || uOK80 m c

theorem least_lt_UbD {y p m : ℕ} (hy : 0 < y) (hp : 0 < p) (hcyc : T^[p] y = y)
    (hleast : ∀ j, y ≤ T^[j] y) (c : ShapeCert) (hm : numLocalMin y p = m)
    (hK : oddCount T y p = c.K) (hP : p = c.P) (hok : uOKD m c = true) : (y : ℝ) < c.Ub := by
  unfold uOKD at hok
  rw [Bool.or_eq_true] at hok
  rcases hok with h | h
  · exact least_lt_Ub hy hp hcyc hleast c hm hK hP h
  · exact least_lt_Ub80 hy hp hcyc hleast c hm hK hP h

/-- **The certificate check for one shape** with the three-term chain. -/
def shapeOK3D (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (c : ShapeCert) : Bool :=
  uOKD m c && (decide (c.Ub ≤ 2 ^ 71 + 1) ||
    (decide (1 ≤ c.Q) && decide (c.Ub ^ c.Q ≤ 2 ^ c.Pe) &&
      decide (chainSum3 S g2 g3 m (c.Y0 S) (chainF (c.Y0 S)) (chainNext S g2 (c.Y0 S) (chainF (c.Y0 S)))
        0 < c.K * 2 ^ S)))

/-- **The exclusion of one shape** with two- and three-rise grids. -/
theorem shape_false3D {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hlow : ∀ j, 2 ^ 71 < T^[j] x) {m S : ℕ} {g2 g3 : List (ℕ × ℕ)}
    (hgrid2 : ∀ e ∈ g2, TwoRiseBound e.1 e.2) (hgrid3 : ∀ e ∈ g3, ThreeRiseBound e.1 e.2)
    (hS : S ≤ 60) (c : ShapeCert)
    (hm : numLocalMin x p = m) (hK : oddCount T x p = c.K) (hP : p = c.P)
    (hok : shapeOK3D m S g2 g3 c = true) : False := by
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
  simp only [shapeOK3D, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hu, hrest⟩ := hok
  have hlt := least_lt_UbD hy hp hcy hleasty c hmy hKy hP hu
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
def certsOK3D (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (certs : List ShapeCert)
    (shapes : List (ℕ × ℕ)) : Bool :=
  shapes.all (fun s => certs.any (fun c => c.K == s.1 && c.P == s.2 && shapeOK3D m S g2 g3 c))

theorem certsOK3D_append (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (certs : List ShapeCert)
    (l₁ l₂ : List (ℕ × ℕ)) :
    certsOK3D m S g2 g3 certs (l₁ ++ l₂) =
      (certsOK3D m S g2 g3 certs l₁ && certsOK3D m S g2 g3 certs l₂) := by
  simp only [certsOK3D, List.all_append]

/-- **The check for one `m`** (Alick's `mOK` with `certsOK3`). -/
def mOK3D (m S : ℕ) (g2 g3 : List (ℕ × ℕ)) (D : MData) : Bool :=
  chainOKX mX₀ m 1 D.boot D.Ks && rhinOK m D.Kceil D.V D.cexp D.kexp &&
    epsOKX mX₀ m D.Ks D.root &&
    decide (0 < D.rb ∧ 0 < D.rd ∧ D.rc * D.rb = D.ra * D.rd + 1 ∧
      (D.ra : ℚ) / D.rb ≤ deltaLo ∧ deltaHi + D.root.eps ≤ (D.rc : ℚ) / D.rd) &&
    D.stair.all (fun e => epsOKX mX₀ m e.1 e.2) &&
    !(D.shapes.contains ((0 : ℕ), (0 : ℕ))) && certsOK3D m S g2 g3 D.certs D.shapes

/-- **Soundness of the check for one `m`**: no nontrivial cycle with `m` local minima has all its
elements above `2⁷¹`, given `RhinBound` and the two- and three-rise bounds of the grids. -/
theorem mOK3D_sound (hR : RhinBound) {m S : ℕ} {g2 g3 : List (ℕ × ℕ)}
    (hgrid2 : ∀ e ∈ g2, TwoRiseBound e.1 e.2) (hgrid3 : ∀ e ∈ g3, ThreeRiseBound e.1 e.2)
    (hS : S ≤ 60) {D : MData}
    (hok : mOK3D m S g2 g3 D = true) {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hm : numLocalMin x p = m) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    False := by
  simp only [mOK3D, certsOK3D, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
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
  exact shape_false3D hx hp hcyc hlow hgrid2 hgrid3 hS c hm hcK.symm hcP.symm hshape

end Collatz
