import Collatz.HercherAll
import Collatz.LogTwoThreeBounds80

/-!
# Replacing `RhinBound` by a much weaker effective measure (`EffMeasure`)

`RhinBound` (Simons–de Weger's Lemma 12, from Rhin's measure) is used only for the ceilings
`K < Kceil(m)` (`K_lt_of_rhinOK`). This file proves the same ceilings (`K_lt_of_ceilOK`) from the far
weaker hypothesis

  `EffMeasure`: `|p log 2 − K log 3| > exp(−K / 2⁸⁰)` for all `p` and all `K ≥ 10³⁶`,

which says only that `log₂ 3` has no rational approximations at the exponential rate `2⁻⁸⁰` beyond
`10³⁶`. Any effective irrationality measure for `log 3 / log 2` implies it with enormous room; for
Rhin's form see `effMeasure_of_rhinAll`.

The range `Kf ≤ K < 10³⁶` needs no transcendence input. Lemma 7 gives `Λ < 2m · 2^{−K/G_m}`. If
`a/b < δ < c/d` are Farey neighbours (here consecutive convergents of `δ`) and `K < b + d`, every
`p/K > δ` has `p/K ≥ c/d`, so `Λ ≥ log 2 · K (c/d − δ)`. The 73 segments `fareySegs` (the last with
`b + d > 10³⁶`) and the 80-digit enclosure of `δ` make this a rational check (`ceilOK`), evaluated
by the kernel. Above `10³⁶`, `EffMeasure` and Lemma 7 give `v (log 2 − G/2⁸⁰) < 2m` with
`v = K/G ≥ 1024`, which is false.
-/

namespace Collatz

open Finset

/-- **The effective-measure hypothesis.** `|p log 2 − K log 3| > exp(−K/2⁸⁰)` for every `p` and
every `K ≥ 10³⁶`. -/
def EffMeasure : Prop :=
  ∀ p K : ℕ, 10 ^ 36 ≤ K →
    Real.exp (-((K : ℝ) / 2 ^ 80)) < |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3|

/-- A Rhin-type measure `|p log 2 − K log 3| > exp(−13.3 (0.46057 + log K))` for all `p` and
`K ≥ 1` (the shape of Simons–de Weger's Lemma 12, without the restriction to cycles). Only used to
show that `EffMeasure` is weaker (`effMeasure_of_rhinAll`); no main theorem assumes it. -/
def RhinAll : Prop :=
  ∀ p K : ℕ, 1 ≤ K →
    Real.exp (-(133 / 10 * (46057 / 100000 + Real.log K))) <
      |(p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3|

theorem log_two_gt_q : (6931471803 / 10 ^ 10 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  have e : (0.6931471803 : ℝ) = 6931471803 / 10 ^ 10 := by norm_num
  linarith

theorem log_two_lt_q : Real.log 2 < 6931471808 / 10 ^ 10 := by
  have h := Real.log_two_lt_d9
  have e : (0.6931471808 : ℝ) = 6931471808 / 10 ^ 10 := by norm_num
  linarith

/-- `EffMeasure` is implied by the Rhin-type measure. -/
theorem effMeasure_of_rhinAll (h : RhinAll) : EffMeasure := by
  intro p K hK
  have hK1 : 1 ≤ K := le_trans (Nat.one_le_pow _ _ (by norm_num)) hK
  refine lt_of_le_of_lt ?_ (h p K hK1)
  apply Real.exp_le_exp.mpr
  have hKR : ((10 : ℝ) ^ 36) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith [show (0 : ℝ) < 10 ^ 36 by norm_num]
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K / 2 ^ 90 by positivity)
  rw [Real.log_div hKpos.ne' (by norm_num), Real.log_pow] at hl
  have hl2 := log_two_lt_q
  have hlog : Real.log K ≤ 90 * (6931471808 / 10 ^ 10) + K / 2 ^ 90 - 1 := by
    push_cast at hl
    linarith
  have h2 : (2 : ℝ) ^ 90 = 2 ^ 10 * 2 ^ 80 := by norm_num
  have hK80 : (K : ℝ) / 2 ^ 90 = (K / 2 ^ 80) / 1024 := by rw [h2]; ring
  rw [hK80] at hlog
  have hbig : (10 : ℝ) ^ 36 / 2 ^ 80 ≤ K / 2 ^ 80 := by
    apply div_le_div_of_nonneg_right hKR (by positivity)
  have hnum : (900 : ℝ) ≤ 10 ^ 36 / 2 ^ 80 := by norm_num
  linarith

/-! ### The rational check -/

/-- A Farey pair `a/b < c/d` (`c b − a d = 1`). -/
structure FSeg where
  a : ℤ
  b : ℕ
  c : ℤ
  d : ℕ

/-- A natural upper bound for a rational: `⌊q⌋ + 1`. -/
def ratCeil (q : ℚ) : ℕ := (q.num / (q.den : ℤ)).toNat + 1

theorem le_ratCeil (q : ℚ) : q ≤ (ratCeil q : ℚ) := by
  have hden : (0 : ℤ) < q.den := by exact_mod_cast q.pos
  have h1 : q.num < (q.num / q.den + 1) * q.den := Int.lt_ediv_add_one_mul_self _ hden
  have h2 : q.num / (q.den : ℤ) ≤ ((q.num / q.den).toNat : ℤ) := Int.self_le_toNat _
  have hdenQ : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have h1Q : (q.num : ℚ) < (((q.num / q.den : ℤ) : ℚ) + 1) * q.den := by exact_mod_cast h1
  have h2Q : ((q.num / q.den : ℤ) : ℚ) ≤ ((q.num / q.den).toNat : ℚ) := by
    have h3 : (((q.num / q.den).toNat : ℤ) : ℚ) = ((q.num / q.den).toNat : ℚ) :=
      Int.cast_natCast _
    rw [← h3]
    exact_mod_cast h2
  have hq : q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
  have key : (q.num : ℚ) / q.den ≤ ((q.num / q.den).toNat : ℚ) + 1 := by
    rw [div_le_iff₀ hdenQ]
    nlinarith
  unfold ratCeil
  push_cast
  calc q = (q.num : ℚ) / q.den := hq
    _ ≤ _ := key

/-- One segment `[L, b + d)`: the Farey pair is valid against the 80-digit enclosure, and
`0.6931471803 · L (c/d − δ⁺) · 2^V > 2m` with `V = min(⌊L/G⌋, 1024)`. -/
def segOK (m Gc L : ℕ) (s : FSeg) : Bool :=
  decide (0 < s.b ∧ 0 < s.d ∧ s.c * s.b - s.a * s.d = 1 ∧ (s.a : ℚ) / s.b ≤ deltaLo80 ∧
    deltaHi80 < (s.c : ℚ) / s.d ∧ 1 ≤ min (L / Gc) 1024 ∧
    (2 * m : ℚ) < 6931471803 / 10 ^ 10 * L * ((s.c : ℚ) / s.d - deltaHi80) *
      2 ^ (min (L / Gc) 1024))

/-- The tail `K ≥ L ≥ 10³⁶` against `EffMeasure`: `V (0.6931471803 − G/2⁸⁰) ≥ 2m`. -/
def tailOK (m Gc L : ℕ) : Bool :=
  decide (10 ^ 36 ≤ L ∧ 1 ≤ min (L / Gc) 1024 ∧
    (2 * m : ℚ) ≤ ((min (L / Gc) 1024 : ℕ) : ℚ) * (6931471803 / 10 ^ 10 - (Gc : ℚ) / 2 ^ 80))

/-- The segments from `K ≥ L` on (segments ending at or below `L` are skipped), then the tail. -/
def ceilChain (m Gc : ℕ) : ℕ → List FSeg → Bool
  | L, [] => tailOK m Gc L
  | L, s :: rest =>
    if s.b + s.d ≤ L then ceilChain m Gc L rest
    else segOK m Gc L s && ceilChain m Gc (s.b + s.d) rest

/-- Consecutive convergents of `δ = log₂ 3` as Farey pairs `(lower, upper)`, from `1/1 < 2/1` to
denominators beyond `10³⁶` (`computed/target14_norhin/segs.py`). -/
def fareySegs : List FSeg := [
  ⟨1, 1, 2, 1⟩,
  ⟨3, 2, 2, 1⟩,
  ⟨3, 2, 8, 5⟩,
  ⟨19, 12, 8, 5⟩,
  ⟨19, 12, 65, 41⟩,
  ⟨84, 53, 65, 41⟩,
  ⟨84, 53, 485, 306⟩,
  ⟨1054, 665, 485, 306⟩,
  ⟨1054, 665, 24727, 15601⟩,
  ⟨50508, 31867, 24727, 15601⟩,
  ⟨50508, 31867, 125743, 79335⟩,
  ⟨176251, 111202, 125743, 79335⟩,
  ⟨176251, 111202, 301994, 190537⟩,
  ⟨16785921, 10590737, 301994, 190537⟩,
  ⟨16785921, 10590737, 17087915, 10781274⟩,
  ⟨85137581, 53715833, 17087915, 10781274⟩,
  ⟨85137581, 53715833, 272500658, 171928773⟩,
  ⟨357638239, 225644606, 272500658, 171928773⟩,
  ⟨357638239, 225644606, 630138897, 397573379⟩,
  ⟨9809721694, 6189245291, 630138897, 397573379⟩,
  ⟨9809721694, 6189245291, 10439860591, 6586818670⟩,
  ⟨103768467013, 65470613321, 10439860591, 6586818670⟩,
  ⟨103768467013, 65470613321, 217976794617, 137528045312⟩,
  ⟨1193652440098, 753110839881, 217976794617, 137528045312⟩,
  ⟨1193652440098, 753110839881, 8573543875303, 5409303924479⟩,
  ⟨9767196315401, 6162414764360, 8573543875303, 5409303924479⟩,
  ⟨9767196315401, 6162414764360, 18340740190704, 11571718688839⟩,
  ⟨83130157078217, 52449289519716, 18340740190704, 11571718688839⟩,
  ⟨83130157078217, 52449289519716, 683381996816440, 431166034846567⟩,
  ⟨766512153894657, 483615324366283, 683381996816440, 431166034846567⟩,
  ⟨766512153894657, 483615324366283, 9115015689657667, 5750934602875680⟩,
  ⟨9881527843552324, 6234549927241963, 9115015689657667, 5750934602875680⟩,
  ⟨9881527843552324, 6234549927241963, 206745572560704147, 130441933147714940⟩,
  ⟨423372672964960618, 267118416222671843, 206745572560704147, 130441933147714940⟩,
  ⟨423372672964960618, 267118416222671843, 630118245525664765, 397560349370386783⟩,
  ⟨6724555128221608268, 4242721909926539673, 630118245525664765, 397560349370386783⟩,
  ⟨6724555128221608268, 4242721909926539673, 7354673373747273033, 4640282259296926456⟩,
  ⟨36143248623210700400, 22803850947114245497, 7354673373747273033, 4640282259296926456⟩,
  ⟨36143248623210700400, 22803850947114245497, 43497921996957973433, 27444133206411171953⟩,
  ⟨79641170620168673833, 50247984153525417450, 43497921996957973433, 27444133206411171953⟩,
  ⟨79641170620168673833, 50247984153525417450, 123139092617126647266, 77692117359936589403⟩,
  ⟨202780263237295321099, 127940101513462006853, 123139092617126647266, 77692117359936589403⟩,
  ⟨202780263237295321099, 127940101513462006853, 325919355854421968365, 205632218873398596256⟩,
  ⟨12261796429850908150604, 7736332199829210068325, 325919355854421968365, 205632218873398596256⟩,
  ⟨12261796429850908150604, 7736332199829210068325, 49373105075258054570781, 31150961018190238869556⟩,
  ⟨2727782575569043909543559, 1721039188200292347893905, 49373105075258054570781, 31150961018190238869556⟩,
  ⟨2727782575569043909543559, 1721039188200292347893905, 2777155680644301964114340, 1752190149218482586763461⟩,
  ⟨5504938256213345873657899, 3473229337418774934657366, 2777155680644301964114340, 1752190149218482586763461⟩,
  ⟨5504938256213345873657899, 3473229337418774934657366, 272519130235098249773351391, 171940427682738454384974395⟩,
  ⟨278024068491311595647009290, 175413657020157229319631761, 272519130235098249773351391, 171940427682738454384974395⟩,
  ⟨278024068491311595647009290, 175413657020157229319631761, 550543198726409845420360681, 347354084702895683704606156⟩,
  ⟨828567267217721441067369971, 522767741723052913024237917, 550543198726409845420360681, 347354084702895683704606156⟩,
  ⟨828567267217721441067369971, 522767741723052913024237917, 3864812267597295609689840565, 2438425051595107335801557824⟩,
  ⟨4693379534815017050757210536, 2961192793318160248825795741, 3864812267597295609689840565, 2438425051595107335801557824⟩,
  ⟨4693379534815017050757210536, 2961192793318160248825795741, 17944950872042346761961472173, 11322003431549588082278945047⟩,
  ⟨40583281278899710574680154882, 25605199656417336413383685835, 17944950872042346761961472173, 11322003431549588082278945047⟩,
  ⟨40583281278899710574680154882, 25605199656417336413383685835, 139694794708741478486001936819, 88137602400801597322430002552⟩,
  ⟨459667665405124146032685965339, 290018006858822128380673693491, 139694794708741478486001936819, 88137602400801597322430002552⟩,
  ⟨459667665405124146032685965339, 290018006858822128380673693491, 599362460113865624518687902158, 378155609259623725703103696043⟩,
  ⟨3456479965974452268626125476129, 2180796053156940756896192173706, 599362460113865624518687902158, 378155609259623725703103696043⟩,
  ⟨3456479965974452268626125476129, 2180796053156940756896192173706, 55903041915705101922536695520222, 35270892459770675836042178475339⟩,
  ⟨115262563797384656113699516516573, 72722580972698292428980549124384, 55903041915705101922536695520222, 35270892459770675836042178475339⟩,
  ⟨115262563797384656113699516516573, 72722580972698292428980549124384, 401690733307859070263635245069941, 253438635377865553122983825848491⟩,
  ⟨516953297105243726377334761586514, 326161216350563845551964374972875, 401690733307859070263635245069941, 253438635377865553122983825848491⟩,
  ⟨516953297105243726377334761586514, 326161216350563845551964374972875, 918644030413102796640970006656455, 579599851728429398674948200821366⟩,
  ⟨1435597327518346523018304768242969, 905761068078993244226912575794241, 918644030413102796640970006656455, 579599851728429398674948200821366⟩,
  ⟨1435597327518346523018304768242969, 905761068078993244226912575794241, 2354241357931449319659274774899424, 1485360919807422642901860776615607⟩,
  ⟨3789838685449795842677579543142393, 2391121987886415887128773352409848, 2354241357931449319659274774899424, 1485360919807422642901860776615607⟩,
  ⟨3789838685449795842677579543142393, 2391121987886415887128773352409848, 21303434785180428533047172490611389, 13440970859239502078545727538664847⟩,
  ⟨46396708255810652908771924524365171, 29273063706365420044220228429739542, 21303434785180428533047172490611389, 13440970859239502078545727538664847⟩,
  ⟨46396708255810652908771924524365171, 29273063706365420044220228429739542, 67700143040991081441819097014976560, 42714034565604922122765955968404389⟩,
  ⟨181796994337792815792410118554318291, 114701132837575264289752140366548320, 67700143040991081441819097014976560, 42714034565604922122765955968404389⟩,
  ⟨181796994337792815792410118554318291, 114701132837575264289752140366548320, 1522076097743333607781100045449522888, 960323097266207036440783078900790949⟩]

/-- **The ceiling check for `m` minima above `K ≥ Kf`.** -/
def ceilOK (m Kf : ℕ) : Bool :=
  ceilChain m (ratCeil (geomQ deltaUp m)) Kf fareySegs

/-! ### Soundness -/

/-- Lemma 7 (Theorem 21, vertex-free, `m₂ = m`) in the form used here: with `v G = K`,
`G ≤ ⌈G_m⌉`, `Λ < 2m / 2^v` once `v ≥ 1`. -/
theorem cycle_ctx {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) {m : ℕ}
    (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) :
    ∃ v G : ℝ, 0 < G ∧ G ≤ (ratCeil (geomQ deltaUp m) : ℝ) ∧ v * G = oddCount T x p ∧
      (1 ≤ v → (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 <
        2 * m / (2 : ℝ) ^ v) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨G, hG⟩ : ∃ G, G = ∑ d ∈ range m, Real.logb 2 3 ^ d := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hG]; exact geomSum_delta_pos hm1
  have hδ0 : (0 : ℝ) ≤ Real.logb 2 3 := by linarith [one_le_logb_two_three]
  have hGhi : G ≤ ((geomQ deltaUp m : ℚ) : ℝ) := by
    rw [hG, geomQ_eq]
    push_cast
    exact sum_le_sum (fun d _ => pow_le_pow_left₀ hδ0 logb_le_deltaUp d)
  have hGc : ((geomQ deltaUp m : ℚ) : ℝ) ≤ (ratCeil (geomQ deltaUp m) : ℝ) := by
    have := le_ratCeil (geomQ deltaUp m)
    exact_mod_cast this
  have h21 := theorem21_vertexFree hx hp hcyc (m₂ := m) hm1 (by omega)
    (X₀ := 1) one_pos (fun j => by exact_mod_cast Nat.succ_le_of_lt (iterate_T_pos hx j))
  rw [hm] at h21
  refine ⟨windowExp m m (oddCount T x p), G, hGpos, le_trans hGhi hGc, ?_, ?_⟩
  · rw [windowExp, ← hG, div_mul_eq_mul_div, div_eq_iff (mul_pos hmR hGpos).ne']
    ring
  · intro hv1
    obtain ⟨v, hv⟩ : ∃ v, v = windowExp m m (oddCount T x p) := ⟨_, rfl⟩
    rw [← hv] at h21 ⊢
    have z : ((m - m : ℕ) : ℝ) = 0 := by rw [Nat.sub_self, Nat.cast_zero]
    rw [z] at h21
    have h2v2 : (2 : ℝ) ≤ (2 : ℝ) ^ v := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) (hv ▸ hv1)
      rwa [Real.rpow_one] at this
    have e : 3 * (m : ℝ) / ((2 : ℝ) ^ v - 1) = 3 * ((m : ℝ) / ((2 : ℝ) ^ v - 1)) := by ring
    have hΛlt : (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 <
        (m : ℝ) / ((2 : ℝ) ^ v - 1) := by
      linarith
    have h1 : (m : ℝ) / ((2 : ℝ) ^ v - 1) ≤ 2 * m / (2 : ℝ) ^ v := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have := mul_le_mul_of_nonneg_left h2v2 hmR.le
      linarith
    linarith

/-- `Λ = log 2 · (p − K δ)`. -/
theorem lambda_eq (p K : ℕ) : (p : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3 =
    Real.log 2 * ((p : ℝ) - K * Real.logb 2 3) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.logb]
  field_simp

/-- `V = min(⌊L/Gc⌋, 1024) ≤ v` when `L ≤ K = v G` and `G ≤ Gc`. -/
theorem V_le_v {L Gc K : ℕ} {v G : ℝ} (hLK : L ≤ K) (hG : 0 < G) (hGc : G ≤ (Gc : ℝ))
    (hvK : v * G = K) : ((min (L / Gc) 1024 : ℕ) : ℝ) ≤ v := by
  have h1 : (min (L / Gc) 1024) * Gc ≤ L :=
    le_trans (Nat.mul_le_mul_right _ (min_le_left _ _)) (Nat.div_mul_le_self L Gc)
  have h1R : ((min (L / Gc) 1024 : ℕ) : ℝ) * (Gc : ℝ) ≤ (K : ℝ) := by
    have : ((min (L / Gc) 1024 * Gc : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans h1 hLK
    rwa [Nat.cast_mul] at this
  have hV0 : (0 : ℝ) ≤ ((min (L / Gc) 1024 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : ((min (L / Gc) 1024 : ℕ) : ℝ) * G ≤ v * G := by
    rw [hvK]
    have := mul_le_mul_of_nonneg_left hGc hV0
    linarith
  exact le_of_mul_le_mul_right h2 hG

/-- **Soundness of the segments and the tail.** -/
theorem ceilChain_sound (hE : EffMeasure) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) {m : ℕ} (hm : numLocalMin x p = m) (hm1 : 1 ≤ m) :
    ∀ (segs : List FSeg) (L : ℕ), L ≤ oddCount T x p →
      ceilChain m (ratCeil (geomQ deltaUp m)) L segs = true → False := by
  obtain ⟨v, G, hG, hGc, hvK, hlam⟩ := cycle_ctx hx hp hcyc hm hm1
  generalize ratCeil (geomQ deltaUp m) = Gc at hGc ⊢
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl2 := log_two_gt_q
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `δ < p/K` once `K > 0`
  have hratio : 0 < oddCount T x p → Real.logb 2 3 < (p : ℝ) / oddCount T x p :=
    fun hK0 => logb_lt_ratio hx hp hcyc hK0
  intro segs
  induction segs with
  | nil =>
    intro L hLK h
    obtain ⟨V, hV⟩ : ∃ V, V = min (L / Gc) 1024 := ⟨_, rfl⟩
    simp only [ceilChain, tailOK, ← hV, decide_eq_true_eq] at h
    obtain ⟨hL0, hV1, hineq⟩ := h
    have hVv : (V : ℝ) ≤ v := hV ▸ V_le_v hLK hG hGc hvK
    have hV1R : (1 : ℝ) ≤ V := by exact_mod_cast hV1
    have hv1 : 1 ≤ v := le_trans hV1R hVv
    have hΛ := hlam hv1
    have hK0 : 10 ^ 36 ≤ oddCount T x p := le_trans hL0 hLK
    have hKpos : 0 < oddCount T x p := lt_of_lt_of_le (by positivity) hK0
    have hKR : (0 : ℝ) < oddCount T x p := by exact_mod_cast hKpos
    have hEK := hE p (oddCount T x p) hK0
    have hineqR : 2 * (m : ℝ) ≤ (V : ℝ) * (6931471803 / 10 ^ 10 - (Gc : ℝ) / 2 ^ 80) := by
      have := (Rat.cast_le (K := ℝ)).mpr hineq
      push_cast at this
      exact this
    -- `Λ > 0`
    have hr := hratio hKpos
    have hpK : (oddCount T x p : ℝ) * Real.logb 2 3 < p := by
      rwa [lt_div_iff₀ hKR, mul_comm] at hr
    have hpos : 0 < (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 := by
      rw [lambda_eq]
      exact mul_pos hl2pos (by linarith)
    rw [abs_of_pos hpos] at hEK
    -- `exp(−K/2⁸⁰) · 2^v < 2m`
    have h2v : (2 : ℝ) ^ v = Real.exp (Real.log 2 * v) := Real.rpow_def_of_pos (by norm_num) v
    have h2vpos : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
    have hlt : Real.exp (-((oddCount T x p : ℝ) / 2 ^ 80)) * (2 : ℝ) ^ v < 2 * m := by
      have := lt_trans hEK hΛ
      rwa [lt_div_iff₀ h2vpos] at this
    rw [h2v, ← Real.exp_add] at hlt
    have hexp := Real.add_one_le_exp (-((oddCount T x p : ℝ) / 2 ^ 80) + Real.log 2 * v)
    -- `K = v G ≤ v Gc`
    have hv0 : (0 : ℝ) ≤ v := by linarith
    have hKle : (oddCount T x p : ℝ) ≤ v * Gc := by
      rw [← hvK]; exact mul_le_mul_of_nonneg_left hGc hv0
    have hKdiv : (oddCount T x p : ℝ) / 2 ^ 80 ≤ v * Gc / 2 ^ 80 :=
      div_le_div_of_nonneg_right hKle (by positivity)
    have hlv : 6931471803 / 10 ^ 10 * v ≤ Real.log 2 * v := mul_le_mul_of_nonneg_right hl2.le hv0
    -- `α = 0.6931471803 − Gc/2⁸⁰ > 0` and `v α ≥ V α ≥ 2m`
    have hVnn : (0 : ℝ) ≤ V := by linarith
    have hα : 0 < (6931471803 / 10 ^ 10 - (Gc : ℝ) / 2 ^ 80) := by
      by_contra hα
      push Not at hα
      have := mul_nonpos_of_nonneg_of_nonpos hVnn hα
      linarith
    have hvα := mul_le_mul_of_nonneg_right hVv hα.le
    have e : v * Gc / 2 ^ 80 = v * ((Gc : ℝ) / 2 ^ 80) := by ring
    nlinarith
  | cons s rest ih =>
    intro L hLK h
    simp only [ceilChain] at h
    split_ifs at h with hs
    · exact ih L hLK h
    rw [Bool.and_eq_true] at h
    by_cases hK : s.b + s.d ≤ oddCount T x p
    · exact ih _ hK h.2
    push Not at hK
    have hseg := h.1
    obtain ⟨V, hV⟩ : ∃ V, V = min (L / Gc) 1024 := ⟨_, rfl⟩
    simp only [segOK, ← hV, decide_eq_true_eq] at hseg
    obtain ⟨hb, hd, hF, ha, hc, hV1, hineq⟩ := hseg
    have hVv : (V : ℝ) ≤ v := hV ▸ V_le_v hLK hG hGc hvK
    have hV1R : (1 : ℝ) ≤ V := by exact_mod_cast hV1
    have hv1 : 1 ≤ v := le_trans hV1R hVv
    have hΛ := hlam hv1
    -- `L ≥ 1`, so `K > 0`
    have hL1 : 1 ≤ L := by
      have := Nat.div_le_self L Gc
      have := min_le_left (L / Gc) 1024
      omega
    have hKpos : 0 < oddCount T x p := lt_of_lt_of_le hL1 hLK
    have hKR : (0 : ℝ) < oddCount T x p := by exact_mod_cast hKpos
    have hr := hratio hKpos
    -- `p/K ≥ c/d`
    have hcd : (s.c : ℝ) / s.d ≤ (p : ℝ) / oddCount T x p := by
      by_contra hlt
      push Not at hlt
      have hlo : (s.a : ℝ) / s.b < (p : ℝ) / oddCount T x p := by
        have h1 : (s.a : ℝ) / s.b ≤ (deltaLo80 : ℝ) := by exact_mod_cast ha
        linarith [deltaLo80_lt_logb]
      have hloQ : (s.a : ℚ) / s.b < (p : ℚ) / oddCount T x p := by
        have : (((s.a : ℚ) / s.b : ℚ) : ℝ) < (((p : ℚ) / oddCount T x p : ℚ) : ℝ) := by
          push_cast; exact hlo
        exact Rat.cast_lt.mp this
      have hhiQ : (p : ℚ) / oddCount T x p < (s.c : ℚ) / s.d := by
        have : (((p : ℚ) / oddCount T x p : ℚ) : ℝ) < (((s.c : ℚ) / s.d : ℚ) : ℝ) := by
          push_cast; exact hlt
        exact Rat.cast_lt.mp this
      have := farey_den_bound_div hKpos hb hd hF hloQ hhiQ
      omega
    -- `p − K δ ≥ K (c/d − δ⁺) ≥ L g`
    have hgap : (deltaHi80 : ℝ) < (s.c : ℝ) / s.d := by exact_mod_cast hc
    set g : ℝ := (s.c : ℝ) / s.d - (deltaHi80 : ℝ) with hg
    have hg0 : 0 < g := by rw [hg]; linarith
    have hδhi := logb_lt_deltaHi80
    have hpK : (oddCount T x p : ℝ) * ((s.c : ℝ) / s.d) ≤ p := by
      rwa [le_div_iff₀ hKR, mul_comm] at hcd
    have hLR : (L : ℝ) ≤ oddCount T x p := by exact_mod_cast hLK
    have hdiff : (L : ℝ) * g ≤ (p : ℝ) - oddCount T x p * Real.logb 2 3 := by
      have h1 : (L : ℝ) * g ≤ (oddCount T x p : ℝ) * g := mul_le_mul_of_nonneg_right hLR hg0.le
      have h2 : (oddCount T x p : ℝ) * g ≤
          (oddCount T x p : ℝ) * ((s.c : ℝ) / s.d - Real.logb 2 3) :=
        mul_le_mul_of_nonneg_left (by rw [hg]; linarith) hKR.le
      nlinarith
    have hLg0 : (0 : ℝ) ≤ L * g := mul_nonneg (Nat.cast_nonneg _) hg0.le
    have hΛlow : 6931471803 / 10 ^ 10 * (L * g) ≤
        (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 := by
      rw [lambda_eq]
      have h1 := mul_le_mul_of_nonneg_right hl2.le hLg0
      have h2 := mul_le_mul_of_nonneg_left hdiff hl2pos.le
      nlinarith
    -- `2^V ≤ 2^v`
    have h2V : (2 : ℝ) ^ V ≤ (2 : ℝ) ^ v := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hVv
    have h2Vpos : (0 : ℝ) < (2 : ℝ) ^ V := by positivity
    have hΛV : (p : ℝ) * Real.log 2 - (oddCount T x p : ℝ) * Real.log 3 < 2 * m / (2 : ℝ) ^ V :=
      lt_of_lt_of_le hΛ (div_le_div_of_nonneg_left (by positivity) h2Vpos h2V)
    have hineqR : 2 * (m : ℝ) < 6931471803 / 10 ^ 10 * L * g * (2 : ℝ) ^ V := by
      have := (Rat.cast_lt (K := ℝ)).mpr hineq
      push_cast at this
      rw [hg]
      exact this
    have hfin : 2 * (m : ℝ) / (2 : ℝ) ^ V < 6931471803 / 10 ^ 10 * (L * g) := by
      rw [div_lt_iff₀ h2Vpos]
      linarith
    linarith

/-- **The ceiling from `EffMeasure`.** A nontrivial cycle with `m` local minima has `K < Kf`
whenever `ceilOK m Kf`. Same conclusion as `K_lt_of_rhinOK`, without `RhinBound`. -/
theorem K_lt_of_ceilOK (hE : EffMeasure) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) {m Kf : ℕ} (hm : numLocalMin x p = m)
    (hok : ceilOK m Kf = true) : oddCount T x p < Kf := by
  have hm1 : 1 ≤ m := by rw [← hm]; exact numLocalMin_pos hx hp hcyc
  by_contra hge
  push Not at hge
  exact ceilChain_sound hE hx hp hcyc hm hm1 fareySegs Kf hge hok

end Collatz
