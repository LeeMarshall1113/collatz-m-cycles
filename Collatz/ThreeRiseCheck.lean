import Collatz.TwoRiseCheck
import Mathlib.Tactic.LinearCombination

/-!
# Three consecutive rises from a number below `2^N`: the checker and its soundness

For an odd `n < 2^N` write `n + 1 = a · 2^{k₀}` (`a` odd, `a < 2^A`, `A = N − k₀`, or `A = 1` if
`k₀ = N`), let `ℓ₀, ℓ₁ ≥ 1` be the two following descents and `k₁, k₂` the next rises:

  `3^{k₀} a + 2^{ℓ₀} = 2^{ℓ₀ + k₁} a₁ + 1`,   `3^{k₁} a₁ + 2^{ℓ₁} = 2^{ℓ₁ + k₂} a₂ + 1`.

With `c₀ = 3^{−k₀}`, `c = 3^{−(k₀+k₁)}` modulo `2^W`, `p = ℓ₀ + k₁`, `q = p + ℓ₁` one has
`a ≡ c₀ (1 − 2^{ℓ₀}) + c 2^p (1 − 2^{ℓ₁}) = y − c 2^q (mod 2^{min(W, q + k₂)})`, where
`y = c₀ (1 − 2^{ℓ₀}) + c 2^p` (`dvd3`, `cong_y`). `TripleCond N B k₀` says `k₀ + k₁ + k₂ ≤ B`.
If not, `k₂ ≥ E = max 1 (B + 1 − k₀ − k₁)`, so the bits `A, …, q + E − 1` of `y − c 2^q` vanish.
For each triple `(k₀, ℓ₀, k₁)` the test `tOK` refutes this for every `q > p` exactly as
`TwoRise.kOK` does for every `ℓ` (direct tests, and a bit-parallel window search over all `q < A`
at once). The triples are finite: `ℓ₀` is at most the lowest set bit `≥ A` of `c₀`
(`TwoRise.bit_false`) and `ℓ₀ + k₁` at most the lowest set bit `≥ A` of `c₀ (1 − 2^{ℓ₀})`.
-/

namespace Collatz.ThreeRise

open Collatz.TwoRise

/-! ### The checker -/

/-- The direct test at `2^q = L2`, `D = 2^E`: with `J = D · L2`, `J ≤ W2` and
`(y + c (J − L2)) mod J ≥ A2`, i.e. `y − c 2^q` has a set bit in `[A, q + E)`. -/
def dOK (D A2 W2 y c L2 : Nat) : Bool :=
  Nat.ble (Nat.mul D L2) W2 &&
    Nat.ble A2 (Nat.mod (Nat.add y (Nat.mul c (Nat.sub (Nat.mul D L2) L2))) (Nat.mul D L2))

/-- `dOK` for `L2, 2 L2, …, 2^{cnt−1} L2`. -/
def dRange (D A2 W2 y c cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih L2 => dOK D A2 W2 y c L2 && ih (Nat.mul 2 L2)) cnt

/-- Direct tests for every set bit `2^i` of `mm`, at `2^q = A2 / 2^i`; fuel `f`. -/
def fallback (D A2 W2 y c f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun mm => Nat.beq mm 0)
    (fun _ ih mm => cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt && Nat.beq (Nat.land mm Pt) Pt &&
          dOK D A2 W2 y c (Nat.div A2 Pt) && ih (Nat.xor mm Pt))) f

/-- The pattern test (as `TwoRise.patternCore`): `X = c mod 2^{A+E₁}`, `P` the window of `y` at `A`. -/
def patCore (D A2 W2 y c E1 L M X P s : Nat) : Bool :=
  cond (Nat.blt s E1)
    (Nat.beq (Nat.land (Nat.shiftRight P s) 1) 1 && Nat.beq (Nat.mod P (Nat.pow 2 s)) 0 &&
      fallback D A2 W2 y c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)))
    (Nat.beq P 0 && fallback D A2 W2 y c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)))

/-- `patCore` for `q ∈ [qmin, A − 1]` with its intermediate values. -/
def patOK (D A2 W2 y c A E1 qmin : Nat) : Bool :=
  let L := Nat.add (Nat.sub A qmin) 1
  let P := Nat.mod (Nat.shiftRight y A) (Nat.pow 2 E1)
  patCore D A2 W2 y c E1 L (Nat.sub (Nat.pow 2 L) 1) (Nat.mod c (Nat.pow 2 (Nat.add A E1))) P
    (lowScan P E1 0)

/-- All tests for one triple: `t` (claimed) a set bit of `y >>> A`; `q ∈ [max A (p+1), A + t]`
direct; `q ∈ [p + 1, min A qmin)` direct; `q ∈ [qmin, A)` by the pattern. -/
def tCore (E1 W A A2 W2 y c p D t qmin : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (Nat.shiftRight y A) t) 1) 1 &&
    dRange D A2 W2 y c (Nat.sub (Nat.add (Nat.add A t) 1) (Nat.max A (Nat.add p 1)))
      (Nat.pow 2 (Nat.max A (Nat.add p 1))) &&
    dRange D A2 W2 y c (Nat.sub (Nat.min A qmin) (Nat.add p 1)) (Nat.pow 2 (Nat.add p 1)) &&
    cond (Nat.ble A qmin) true (Nat.ble (Nat.add A E1) W && patOK D A2 W2 y c A E1 qmin)

/-- The test of the triple `(k₀, ℓ₀, k₁)`, `x = c₀ (1 − 2^{ℓ₀}) mod 2^W`, `c = 3^{−(k₀+k₁)}`. -/
def tOK (B E1 W A A2 W2 k0 x l0 k1 c : Nat) : Bool :=
  tCore E1 W A A2 W2 (Nat.mod (Nat.add x (Nat.mul c (Nat.pow 2 (Nat.add l0 k1)))) W2) c
    (Nat.add l0 k1) (Nat.pow 2 (Nat.max 1 (Nat.sub (Nat.add B 1) (Nat.add k0 k1))))
    (lowScan (Nat.shiftRight (Nat.mod (Nat.add x (Nat.mul c (Nat.pow 2 (Nat.add l0 k1)))) W2) A) W 0)
    (Nat.max (Nat.add (Nat.add l0 k1) 1)
      (Nat.sub (Nat.add A E1) (Nat.max 1 (Nat.sub (Nat.add B 1) (Nat.add k0 k1)))))

/-- The loop over `k₁ = k, …, k + cnt − 1`; on entry `c = 3^{−(k₀+k−1)} mod 2^W`. -/
def k1Loop (B E1 W i3 A A2 W2 k0 x l0 cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k1 c =>
      let c' := Nat.mod (Nat.mul c i3) W2
      tOK B E1 W A A2 W2 k0 x l0 k1 c' && ih (Nat.add k1 1) c') cnt

/-- All `k₁` for one `(k₀, ℓ₀)`: `t` (claimed) a set bit of `x >>> A`, `k₁ ≤ A + t − ℓ₀`. -/
def lCore (B E1 W i3 A A2 W2 k0 c0 l0 x t : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (Nat.shiftRight x A) t) 1) 1 && Nat.ble l0 (Nat.add A t) &&
    k1Loop B E1 W i3 A A2 W2 k0 x l0 (Nat.sub (Nat.add A t) l0) 1 c0

/-- `lCore` with its intermediate values. -/
def lBody (B E1 W i3 A A2 W2 k0 c0 l0 : Nat) : Bool :=
  lCore B E1 W i3 A A2 W2 k0 c0 l0 (Nat.mod (Nat.mul c0 (Nat.sub (Nat.add W2 1) (Nat.pow 2 l0))) W2)
    (lowScan (Nat.shiftRight (Nat.mod (Nat.mul c0 (Nat.sub (Nat.add W2 1) (Nat.pow 2 l0))) W2) A) W 0)

/-- The loop over `ℓ₀ = l, …, l + cnt − 1`. -/
def lLoop (B E1 W i3 A A2 W2 k0 c0 cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih l0 => lBody B E1 W i3 A A2 W2 k0 c0 l0 && ih (Nat.add l0 1)) cnt

/-- All tests for one `k₀`: `t` (claimed) a set bit of `c₀ >>> A`, `ℓ₀ ≤ A + t`. -/
def kCore3 (B E1 W i3 k0 c0 A t : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (Nat.shiftRight c0 A) t) 1) 1 &&
    lLoop B E1 W i3 A (Nat.pow 2 A) (Nat.pow 2 W) k0 c0 (Nat.add A t) 1

/-- `kCore3` with its intermediate values (`c₀ = 3^{−k₀} mod 2^W`). -/
def kOK3 (N B E1 W i3 k0 c0 : Nat) : Bool :=
  kCore3 B E1 W i3 k0 c0 (cond (Nat.blt k0 N) (Nat.sub N k0) 1)
    (lowScan (Nat.shiftRight c0 (cond (Nat.blt k0 N) (Nat.sub N k0) 1)) W 0)

/-- The loop over `k₀ = k, …, k + cnt − 1`; on entry `c = 3^{−(k−1)} mod 2^W`. -/
def loop3 (N B E1 W i3 cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := Nat.mod (Nat.mul c i3) (Nat.pow 2 W)
      kOK3 N B E1 W i3 k c' && ih (Nat.add k 1) c') cnt

/-- The checker for `k₀ ∈ [k, k + cnt)` (`k ≥ 1`). -/
def rangeOK3 (N B E1 W i3 k c0 cnt : Nat) : Bool :=
  Nat.ble 1 k && Nat.beq (Nat.mod (Nat.mul 3 i3) (Nat.pow 2 W)) 1 &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 (Nat.sub k 1)) c0) (Nat.pow 2 W)) 1 &&
    loop3 N B E1 W i3 cnt k c0

/-! ### Soundness -/

/-- The three-rise condition for first rise `k₀` below `2^N`. -/
def TripleCond (N B k0 : Nat) : Prop :=
  ∀ a l0 k1 a1 l1 k2 a2, a % 2 = 1 → 2 ^ k0 * a ≤ 2 ^ N → 1 ≤ l0 → 1 ≤ k1 → 1 ≤ l1 → 1 ≤ k2 →
    3 ^ k0 * a + 2 ^ l0 = 2 ^ (l0 + k1) * a1 + 1 →
    3 ^ k1 * a1 + 2 ^ l1 = 2 ^ (l1 + k2) * a2 + 1 → k0 + k1 + k2 ≤ B

theorem pow_split_int {j W : Nat} (h : j ≤ W) : ∃ w : Int, (2 : Int) ^ W = 2 ^ j * w :=
  ⟨2 ^ (W - j), by rw [← pow_add, Nat.add_sub_cancel' h]⟩

/-- **The 2-adic form of three rises**: `a ≡ c₀ (1 − 2^{ℓ₀}) + c 2^{ℓ₀+k₁} (1 − 2^{ℓ₁})`. -/
theorem dvd3 {k0 k1 l0 l1 k2 a a1 a2 c0 c W j : Nat}
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hc : 3 ^ (k0 + k1) * c % 2 ^ W = 1)
    (h0 : 3 ^ k0 * a + 2 ^ l0 = 2 ^ (l0 + k1) * a1 + 1)
    (h1 : 3 ^ k1 * a1 + 2 ^ l1 = 2 ^ (l1 + k2) * a2 + 1)
    (hjW : j ≤ W) (hjJ : j ≤ l0 + k1 + l1 + k2) :
    ((2 ^ j : Nat) : Int) ∣
      (a : Int) - ((c0 : Int) * (1 - 2 ^ l0) + (c : Int) * 2 ^ (l0 + k1) * (1 - 2 ^ l1)) := by
  have hq0 := Nat.div_add_mod (3 ^ k0 * c0) (2 ^ W)
  rw [hc0] at hq0
  have hq := Nat.div_add_mod (3 ^ (k0 + k1) * c) (2 ^ W)
  rw [hc] at hq
  obtain ⟨v, hv⟩ : ∃ v, v = 3 ^ k0 * c0 / 2 ^ W := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = 3 ^ (k0 + k1) * c / 2 ^ W := ⟨_, rfl⟩
  rw [← hv] at hq0
  rw [← hu] at hq
  have e0 : ((2 ^ W * v + 1 : Nat) : Int) = ((3 ^ k0 * c0 : Nat) : Int) := by rw [hq0]
  have e : ((2 ^ W * u + 1 : Nat) : Int) = ((3 ^ (k0 + k1) * c : Nat) : Int) := by rw [hq]
  have r0 : ((3 ^ k0 * a + 2 ^ l0 : Nat) : Int) = ((2 ^ (l0 + k1) * a1 + 1 : Nat) : Int) := by rw [h0]
  have r1 : ((3 ^ k1 * a1 + 2 ^ l1 : Nat) : Int) = ((2 ^ (l1 + k2) * a2 + 1 : Nat) : Int) := by
    rw [h1]
  push_cast at e0 e r0 r1
  obtain ⟨wW, hwW⟩ := pow_split_int hjW
  obtain ⟨wJ, hwJ⟩ := pow_split_int hjJ
  refine ⟨(c : Int) * wJ * a2 - wW * u * a +
    (1 - 2 ^ l0) * ((c0 : Int) * wW * u - (c : Int) * 3 ^ k1 * wW * v), ?_⟩
  push_cast
  linear_combination ((a : Int) + (2 ^ l0 - 1) * (c0 : Int)) * e + (c : Int) * 3 ^ k1 * r0 +
    (c : Int) * 2 ^ (l0 + k1) * r1 - (2 ^ l0 - 1) * (c : Int) * 3 ^ k1 * e0 + (c : Int) * a2 * hwJ +
    (-((u : Int) * a) + (1 - 2 ^ l0) * ((c0 : Int) * u - (c : Int) * 3 ^ k1 * v)) * hwW

/-- The congruence with the checker's `x` and `y`: `a ≡ y − c 2^q (mod 2^j)`. -/
theorem cong_y {k0 k1 l0 l1 k2 a a1 a2 c0 c W x y j : Nat}
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hc : 3 ^ (k0 + k1) * c % 2 ^ W = 1)
    (h0 : 3 ^ k0 * a + 2 ^ l0 = 2 ^ (l0 + k1) * a1 + 1)
    (h1 : 3 ^ k1 * a1 + 2 ^ l1 = 2 ^ (l1 + k2) * a2 + 1)
    (hx : x = c0 * (2 ^ W + 1 - 2 ^ l0) % 2 ^ W) (hl0W : l0 ≤ W)
    (hy : y = (x + c * 2 ^ (l0 + k1)) % 2 ^ W)
    (hjW : j ≤ W) (hjJ : j ≤ l0 + k1 + l1 + k2) :
    ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ (l0 + k1 + l1)) := by
  obtain ⟨w, hw⟩ := dvd3 hc0 hc h0 h1 hjW hjJ
  have ex := Nat.div_add_mod (c0 * (2 ^ W + 1 - 2 ^ l0)) (2 ^ W)
  rw [← hx] at ex
  have ey := Nat.div_add_mod (x + c * 2 ^ (l0 + k1)) (2 ^ W)
  rw [← hy] at ey
  obtain ⟨qx, hqx⟩ : ∃ q, q = c0 * (2 ^ W + 1 - 2 ^ l0) / 2 ^ W := ⟨_, rfl⟩
  obtain ⟨qy, hqy⟩ : ∃ q, q = (x + c * 2 ^ (l0 + k1)) / 2 ^ W := ⟨_, rfl⟩
  rw [← hqx] at ex
  rw [← hqy] at ey
  have hle : 2 ^ l0 ≤ 2 ^ W + 1 := Nat.le_succ_of_le (Nat.pow_le_pow_right (by decide) hl0W)
  have ex' : ((2 ^ W * qx + x : Nat) : Int) = ((c0 * (2 ^ W + 1 - 2 ^ l0) : Nat) : Int) := by rw [ex]
  have ey' : ((2 ^ W * qy + y : Nat) : Int) = ((x + c * 2 ^ (l0 + k1) : Nat) : Int) := by rw [ey]
  push_cast [Nat.cast_sub hle] at ex'
  push_cast at ey' hw ⊢
  obtain ⟨wW, hwW⟩ := pow_split_int hjW
  refine ⟨w - wW * ((c0 : Int) - qx - qy), ?_⟩
  linear_combination (-1 : Int) * ex' + (-1 : Int) * ey' + hw - ((c0 : Int) - qx - qy) * hwW

theorem mod_of_dvd {a y c j q : Nat}
    (h : ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q)) (hqj : q ≤ j) :
    a % 2 ^ j = (y + c * (2 ^ j - 2 ^ q)) % 2 ^ j := by
  apply nat_mod_eq_of_int_dvd
  have hle : 2 ^ q ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hqj
  push_cast [Nat.cast_sub hle]
  obtain ⟨w, hw⟩ := h
  refine ⟨w - c, ?_⟩
  push_cast at hw ⊢
  linear_combination hw

theorem mod_low_of_dvd {a y c j q : Nat}
    (h : ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q)) (hjq : j ≤ q) :
    a % 2 ^ j = y % 2 ^ j := by
  apply nat_mod_eq_of_int_dvd
  obtain ⟨w, hw⟩ := h
  obtain ⟨z, hz⟩ := pow_split_int hjq
  refine ⟨w - c * z, ?_⟩
  push_cast at hw ⊢
  linear_combination hw - (c : Int) * hz

theorem window_of_dvd {a y c q A E : Nat}
    (h : ((2 ^ (A + E) : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q)) :
    y % 2 ^ (A + E) = (a + c * 2 ^ q) % 2 ^ (A + E) := by
  apply nat_mod_eq_of_int_dvd
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  push_cast at hw ⊢
  linear_combination -hw

theorem dOK_iff (D A2 W2 y c L2 : Nat) :
    dOK D A2 W2 y c L2 = true ↔ D * L2 ≤ W2 ∧ A2 ≤ (y + c * (D * L2 - L2)) % (D * L2) := by
  simp only [dOK, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, mod_eq']

/-- The direct test refutes `k₂ ≥ E` at `q`. -/
theorem dOK_false {D A2 W2 y c L2 E A W q a : Nat} (h : dOK D A2 W2 y c L2 = true)
    (hD : D = 2 ^ E) (hA2 : A2 = 2 ^ A) (hW2 : W2 = 2 ^ W) (hL2 : L2 = 2 ^ q) (ha : a < 2 ^ A)
    (hcong : ∀ j, j ≤ W → j ≤ q + E →
      ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q)) : False := by
  rw [dOK_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hJ : D * L2 = 2 ^ (q + E) := by rw [hD, hL2, ← Nat.pow_add, Nat.add_comm]
  rw [hJ, hW2] at h1
  rw [hJ, hA2, hL2] at h2
  have hjW : q + E ≤ W := (Nat.pow_le_pow_iff_right (by decide)).mp h1
  have hm := mod_of_dvd (hcong (q + E) hjW (Nat.le_refl _)) (Nat.le_add_right q E)
  rw [← hm] at h2
  have : a % 2 ^ (q + E) ≤ a := Nat.mod_le _ _
  omega

theorem dRange_succ (D A2 W2 y c cnt L2 : Nat) : dRange D A2 W2 y c (cnt + 1) L2 =
    (dOK D A2 W2 y c L2 && dRange D A2 W2 y c cnt (Nat.mul 2 L2)) := rfl

theorem dRange_sound {D A2 W2 y c : Nat} : ∀ (cnt L2 : Nat),
    dRange D A2 W2 y c cnt L2 = true → ∀ r < cnt, dOK D A2 W2 y c (2 ^ r * L2) = true := by
  intro cnt
  induction cnt with
  | zero => intro L2 _ r hr; omega
  | succ cnt ih =>
    intro L2 h r hr
    rw [dRange_succ, Bool.and_eq_true] at h
    rcases r with _ | r
    · rw [Nat.pow_zero, Nat.one_mul]; exact h.1
    · have := ih _ h.2 r (by omega)
      rwa [Nat.mul_eq, ← Nat.mul_assoc, ← Nat.pow_succ] at this

theorem fallback_zero (D A2 W2 y c mm : Nat) : fallback D A2 W2 y c 0 mm = Nat.beq mm 0 := rfl

theorem fallback_succ (D A2 W2 y c f mm : Nat) : fallback D A2 W2 y c (f + 1) mm =
    cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        Nat.beq (Nat.land Pt (Nat.sub Pt 1)) 0 && Nat.ble 1 Pt && Nat.beq (Nat.land mm Pt) Pt &&
          dOK D A2 W2 y c (Nat.div A2 Pt) && fallback D A2 W2 y c f (Nat.xor mm Pt)) := rfl

theorem fallback_sound {D A2 W2 y c : Nat} : ∀ (f mm : Nat),
    fallback D A2 W2 y c f mm = true →
      ∀ i, mm.testBit i = true → dOK D A2 W2 y c (A2 / 2 ^ i) = true := by
  intro f
  induction f with
  | zero =>
    intro mm h i hi
    rw [fallback_zero, Nat.beq_eq] at h
    subst h
    simp at hi
  | succ f ih =>
    intro mm h i hi
    rw [fallback_succ] at h
    by_cases h0 : mm = 0
    · subst h0; simp at hi
    · have hb : Nat.beq mm 0 = false := by
        cases hq : Nat.beq mm 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h0
      rw [hb] at h
      simp only [Bool.cond_false, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      generalize hPt : Nat.land mm (Nat.xor mm (Nat.sub mm 1)) = Pt at h1 h2 h3 h4 h5
      have hpow : Pt.isPowerOfTwo :=
        (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp h1
      obtain ⟨t, ht⟩ := hpow
      subst ht
      by_cases hit : i = t
      · subst hit; rwa [div_eq'] at h4
      · apply ih _ h5 i
        rw [Nat.xor_eq, Nat.testBit_xor, hi, Nat.testBit_two_pow]
        simp [Ne.symm hit]

theorem patCore_zero_false {D A2 W2 y c E1 L M X P s : Nat}
    (h : patCore D A2 W2 y c E1 L M X P s = true) (hs : E1 ≤ s) :
    P = 0 ∧ fallback D A2 W2 y c L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = false := by
    rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega
  simp only [patCore, hb, Bool.cond_false, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem patCore_lt {D A2 W2 y c E1 L M X P s : Nat}
    (h : patCore D A2 W2 y c E1 L M X P s = true) (hs : s < E1) :
    P.testBit s = true ∧ P % 2 ^ s = 0 ∧ fallback D A2 W2 y c L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = true := by rw [Nat.blt_eq]; exact hs
  simp only [patCore, hb, Bool.cond_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, by rw [mod_eq', pow_eq'] at h2; exact h2, h3⟩
  rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h1
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  simp [h1]

/-- **The pattern test.** If the window of `c` at `i ∈ [1, L − 1]` is `P` or `P − 1`, the direct
test at `2^A / 2^i` has been run and passed. -/
theorem patCore_sound {D A2 W2 y c E1 L P s A i : Nat}
    (h : patCore D A2 W2 y c E1 L (2 ^ L - 1) (c % 2 ^ (A + E1)) P s = true)
    (hi1 : 1 ≤ i) (hiL : i < L) (hiA : i ≤ A)
    (hw : (c >>> i) % 2 ^ E1 = P ∨ ((c >>> i) % 2 ^ E1 + 1) % 2 ^ E1 = P) :
    dOK D A2 W2 y c (A2 / 2 ^ i) = true := by
  have hmask : ((2 ^ L - 1) ^^^ 1).testBit i = true := testBit_xor_one_mask hi1 hiL
  have hX : ∀ j, j < E1 → (c % 2 ^ (A + E1)).testBit (i + j) = c.testBit (i + j) := by
    intro j hj
    rw [Nat.testBit_mod_two_pow]
    have : i + j < A + E1 := by omega
    simp [this]
  have hwlt : (c >>> i) % 2 ^ E1 < 2 ^ E1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases Nat.lt_or_ge s E1 with hs | hs
  · obtain ⟨hPs, hPs0, hf⟩ := patCore_lt h hs
    simp only [Nat.land_eq, Nat.xor_eq, Nat.sub_eq, Nat.add_eq, shiftRight_eq'] at hf
    apply fallback_sound _ _ hf i
    rw [Nat.testBit_and, hmask, Bool.and_true, testBit_matchMask (L := L) rfl]
    refine ⟨hiL, fun b hb => ?_⟩
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      show s + 1 + (i + b) = i + (s + 1 + b) by omega, hX _ (by omega)]
    have hb' : s + 1 + b < E1 := by omega
    rw [← testBit_window (c := c) (i := i) hb']
    rcases hw with hw | hw
    · rw [hw]
    · have hh := high_bits_of_pred hwlt hw hPs hPs0
      have e1 := congrArg (fun x => Nat.testBit x b) hh
      simp only [Nat.testBit_shiftRight] at e1
      exact e1
  · obtain ⟨hP0, hf⟩ := patCore_zero_false h hs
    subst hP0
    simp only [Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.sub_eq, pow_eq'] at hf
    apply fallback_sound _ _ hf i
    rw [Nat.testBit_and, hmask, Bool.and_true, Nat.testBit_or, Bool.or_eq_true,
      testBit_matchMask (L := L) rfl, testBit_matchMask (L := L) rfl]
    rcases hw with hw | hw
    · left
      refine ⟨hiL, fun b hb => ?_⟩
      rw [hX b hb, ← testBit_window (c := c) (i := i) hb, hw]
    · right
      refine ⟨hiL, fun b hb => ?_⟩
      have hw1 : (c >>> i) % 2 ^ E1 = 2 ^ E1 - 1 := by
        rcases Nat.lt_or_ge ((c >>> i) % 2 ^ E1 + 1) (2 ^ E1) with hh | hh
        · rw [Nat.mod_eq_of_lt hh] at hw; omega
        · omega
      rw [hX b hb, ← testBit_window (c := c) (i := i) hb, hw1]

/-- If `y ≡ a + c 2^q (mod 2^{A+E})` with `a < 2^A`, `q ≤ A`, the `E`-bit window of `c` at `A − q`
equals the window of `y` at `A`, or is one less. -/
theorem window_borrow_gen {a y c q A E : Nat}
    (hm : y % 2 ^ (A + E) = (a + c * 2 ^ q) % 2 ^ (A + E)) (hqA : q ≤ A) (ha : a < 2 ^ A) :
    (c >>> (A - q)) % 2 ^ E = (y >>> A) % 2 ^ E ∨
      ((c >>> (A - q)) % 2 ^ E + 1) % 2 ^ E = (y >>> A) % 2 ^ E := by
  obtain ⟨h, hh⟩ : ∃ h, h = c >>> (A - q) := ⟨_, rfl⟩
  have hsp := mul_split hqA hh
  have hpow : 2 ^ (A - q) * 2 ^ q = 2 ^ A := by rw [← Nat.pow_add, Nat.sub_add_cancel hqA]
  have hr : c % 2 ^ (A - q) * 2 ^ q < 2 ^ A := by
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  obtain ⟨u, hu⟩ : ∃ u, u = a + c % 2 ^ (A - q) * 2 ^ q := ⟨_, rfl⟩
  have hu2 : u < 2 * 2 ^ A := by omega
  have hdm := Nat.div_add_mod u (2 ^ A)
  have he : u / 2 ^ A < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hsum : a + c * 2 ^ q = u % 2 ^ A + (h + u / 2 ^ A) * 2 ^ A := by
    rw [hsp, Nat.add_mul]
    have : 2 ^ A * (u / 2 ^ A) = u / 2 ^ A * 2 ^ A := Nat.mul_comm _ _
    omega
  rw [hsum] at hm
  have hwin := win_of_split hm (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [← hh, hwin]
  rcases Nat.lt_or_ge (u / 2 ^ A) 1 with h0 | h1
  · left
    rw [Nat.lt_one_iff.mp h0, Nat.add_zero]
  · right
    rw [Nat.le_antisymm (Nat.lt_succ_iff.mp he) h1]
    exact Nat.mod_add_mod h (2 ^ E) 1

theorem testBit_of_land {y t : Nat} (h : Nat.land (Nat.shiftRight y t) 1 = 1) :
    y.testBit t = true := by
  rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  simp [h]

theorem testBit_lt_of_lt {y z W : Nat} (hy : y < 2 ^ W) (hz : y.testBit z = true) : z < W := by
  rcases Nat.lt_or_ge z W with h | h
  · exact h
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) h))] at hz
    exact absurd hz (by decide)

theorem testBit_small {a A z : Nat} (ha : a < 2 ^ A) (hz : A ≤ z) : a.testBit z = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hz))

/-- **Soundness of the test of one triple**: no `q > p` survives. -/
theorem tCore_sound {E1 W A A2 W2 y c p D t qmin E a q k2 : Nat}
    (h : tCore E1 W A A2 W2 y c p D t qmin = true) (hD : D = 2 ^ E) (hA2 : A2 = 2 ^ A)
    (hW2 : W2 = 2 ^ W) (hqmin : qmin = max (p + 1) (A + E1 - E)) (hyW : y < 2 ^ W)
    (ha : a < 2 ^ A) (hq : p + 1 ≤ q) (hk2 : E ≤ k2)
    (hcong : ∀ j, j ≤ W → j ≤ q + k2 →
      ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q)) : False := by
  simp only [tCore, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hbit, hd1⟩, hd2⟩, hpat⟩ := h
  have em1 : Nat.min A qmin = min A qmin := rfl
  have em2 : Nat.max A (Nat.add p 1) = max A (p + 1) := rfl
  simp only [em1, em2, Nat.sub_eq, Nat.add_eq, pow_eq'] at hd1 hd2
  have hcong' : ∀ j, j ≤ W → j ≤ q + E →
      ((2 ^ j : Nat) : Int) ∣ (a : Int) - ((y : Int) - (c : Int) * 2 ^ q) :=
    fun j h1 h2 => hcong j h1 (by omega)
  have hz : y.testBit (A + t) = true := by
    have h1 := testBit_of_land hbit
    rwa [shiftRight_eq', Nat.testBit_shiftRight] at h1
  have hzW : A + t < W := testBit_lt_of_lt hyW hz
  have hqm1 : p + 1 ≤ qmin := by rw [hqmin]; exact Nat.le_max_left _ _
  have hqm2 : A + E1 - E ≤ qmin := by rw [hqmin]; exact Nat.le_max_right _ _
  rcases Nat.lt_or_ge (A + t) q with hlt | hge
  · -- `q > A + t`: bit `A + t` of `a` would be set
    have hm := mod_low_of_dvd (hcong (A + t + 1) (by omega) (by omega)) hlt
    have e := congrArg (fun x => Nat.testBit x (A + t)) hm
    simp [Nat.testBit_mod_two_pow, testBit_small ha (Nat.le_add_right A t), hz] at e
  rcases Nat.lt_or_ge q A with hqA | hAq
  · rcases Nat.lt_or_ge q qmin with hqm | hqm
    · -- direct, below `qmin`
      have hd := dRange_sound _ _ hd2 (q - (p + 1)) (by omega)
      rw [← Nat.pow_add, show q - (p + 1) + (p + 1) = q by omega] at hd
      exact dOK_false hd hD hA2 hW2 rfl ha hcong'
    · -- the pattern
      have hnb : Nat.ble A qmin = false := by
        rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega
      rw [hnb, Bool.cond_false, Bool.and_eq_true, Nat.ble_eq] at hpat
      obtain ⟨hAE, hp⟩ := hpat
      have hAE' : A + E1 ≤ W := hAE
      have hm := window_of_dvd (E := E1) (hcong (A + E1) hAE' (by omega))
      have hwb := window_borrow_gen hm (Nat.le_of_lt hqA) ha
      simp only [patOK, Nat.add_eq, Nat.sub_eq, pow_eq', mod_eq', shiftRight_eq'] at hp
      have hd := patCore_sound (A := A) (i := A - q) hp (by omega) (by omega) (Nat.sub_le A q) hwb
      have e : A2 / 2 ^ (A - q) = 2 ^ q := by
        rw [hA2, Nat.pow_div (Nat.sub_le A q) (by decide), Nat.sub_sub_self (Nat.le_of_lt hqA)]
      rw [e] at hd
      exact dOK_false hd hD hA2 hW2 rfl ha hcong'
  · -- `max A (p + 1) ≤ q ≤ A + t`: direct
    have hd := dRange_sound _ _ hd1 (q - max A (p + 1)) (by omega)
    rw [← Nat.pow_add, show q - max A (p + 1) + max A (p + 1) = q by omega] at hd
    exact dOK_false hd hD hA2 hW2 rfl ha hcong'

/-- The bound for one triple `(k₀, ℓ₀, k₁)`. -/
def KCond (B A k0 l0 k1 : Nat) : Prop :=
  ∀ a a1 l1 k2 a2, a < 2 ^ A → 1 ≤ l1 → 1 ≤ k2 →
    3 ^ k0 * a + 2 ^ l0 = 2 ^ (l0 + k1) * a1 + 1 →
    3 ^ k1 * a1 + 2 ^ l1 = 2 ^ (l1 + k2) * a2 + 1 → k0 + k1 + k2 ≤ B

theorem tOK_sound {B E1 W A k0 x l0 k1 c c0 : Nat}
    (h : tOK B E1 W A (2 ^ A) (2 ^ W) k0 x l0 k1 c = true)
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hc : 3 ^ (k0 + k1) * c % 2 ^ W = 1)
    (hx : x = c0 * (2 ^ W + 1 - 2 ^ l0) % 2 ^ W) (hl0W : l0 ≤ W) : KCond B A k0 l0 k1 := by
  intro a a1 l1 k2 a2 ha hl1 hk2 h0 h1
  apply Nat.le_of_not_lt
  intro hbad
  obtain ⟨y, hy⟩ : ∃ y, y = (x + c * 2 ^ (l0 + k1)) % 2 ^ W := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = max 1 (B + 1 - (k0 + k1)) := ⟨_, rfl⟩
  have h' : tCore E1 W A (2 ^ A) (2 ^ W) y c (l0 + k1) (2 ^ E)
      (lowScan (y >>> A) W 0) (max (l0 + k1 + 1) (A + E1 - E)) = true := by
    rw [hy, hE]; exact h
  have hyW : y < 2 ^ W := by rw [hy]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hk2E : E ≤ k2 := by rw [hE]; omega
  refine tCore_sound h' rfl rfl rfl rfl hyW ha (q := l0 + k1 + l1) (by omega) hk2E ?_
  intro j hjW hjJ
  exact cong_y hc0 hc h0 h1 hx hl0W hy hjW (by omega)

theorem k1Loop_succ (B E1 W i3 A A2 W2 k0 x l0 cnt k1 c : Nat) :
    k1Loop B E1 W i3 A A2 W2 k0 x l0 (cnt + 1) k1 c =
      (tOK B E1 W A A2 W2 k0 x l0 k1 (Nat.mod (Nat.mul c i3) W2) &&
        k1Loop B E1 W i3 A A2 W2 k0 x l0 cnt (Nat.add k1 1) (Nat.mod (Nat.mul c i3) W2)) := rfl

theorem k1Loop_sound {B E1 W i3 A k0 x l0 c0 : Nat} (hi : 3 * i3 % 2 ^ W = 1)
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hx : x = c0 * (2 ^ W + 1 - 2 ^ l0) % 2 ^ W)
    (hl0W : l0 ≤ W) : ∀ cnt k1 c,
    k1Loop B E1 W i3 A (2 ^ A) (2 ^ W) k0 x l0 cnt k1 c = true →
      3 ^ (k0 + k1 - 1) * c % 2 ^ W = 1 → 1 ≤ k1 →
      ∀ k1', k1 ≤ k1' → k1' < k1 + cnt → KCond B A k0 l0 k1' := by
  intro cnt
  induction cnt with
  | zero => intro k1 c _ _ _ k1' h1 h2; omega
  | succ cnt ih =>
    intro k1 c h hc hk k1' h1 h2
    rw [k1Loop_succ, Bool.and_eq_true] at h
    have hc' := inv_step (k := k0 + k1) hc hi (by omega)
    rcases Nat.eq_or_lt_of_le h1 with he | hlt
    · subst he
      exact tOK_sound h.1 hc0 hc' hx hl0W
    · exact ih (k1 + 1) _ h.2 (by rw [show k0 + (k1 + 1) - 1 = k0 + k1 by omega]; exact hc')
        (by omega) k1' hlt (by omega)

/-- The bound for one `(k₀, ℓ₀)`. -/
def LCond (B A k0 l0 : Nat) : Prop := ∀ k1, 1 ≤ k1 → KCond B A k0 l0 k1

theorem x_mod {c0 W l0 j : Nat} (hjW : j ≤ W) (hl0 : l0 ≤ j) :
    c0 * (2 ^ W + 1 - 2 ^ l0) % 2 ^ W % 2 ^ j = c0 * (2 ^ j + 1 - 2 ^ l0) % 2 ^ j := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hjW)]
  apply nat_mod_eq_of_int_dvd
  have h1 : 2 ^ l0 ≤ 2 ^ W + 1 :=
    Nat.le_succ_of_le (Nat.pow_le_pow_right (by decide) (Nat.le_trans hl0 hjW))
  have h2 : 2 ^ l0 ≤ 2 ^ j + 1 := Nat.le_succ_of_le (Nat.pow_le_pow_right (by decide) hl0)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
  obtain ⟨w, hw⟩ := pow_split_int hjW
  refine ⟨(c0 : Int) * (w - 1), ?_⟩
  push_cast
  linear_combination (c0 : Int) * hw

theorem lBody_sound {B E1 W i3 A k0 c0 l0 : Nat}
    (h : lBody B E1 W i3 A (2 ^ A) (2 ^ W) k0 c0 l0 = true) (hi : 3 * i3 % 2 ^ W = 1)
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hl0W : l0 ≤ W) (hl0 : 1 ≤ l0) : LCond B A k0 l0 := by
  obtain ⟨x, hx⟩ : ∃ x, x = c0 * (2 ^ W + 1 - 2 ^ l0) % 2 ^ W := ⟨_, rfl⟩
  have h' : lCore B E1 W i3 A (2 ^ A) (2 ^ W) k0 c0 l0 x (lowScan (x >>> A) W 0) = true := by
    rw [hx]; exact h
  obtain ⟨t, ht⟩ : ∃ t, t = lowScan (x >>> A) W 0 := ⟨_, rfl⟩
  rw [← ht] at h'
  simp only [lCore, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.add_eq, Nat.sub_eq] at h'
  obtain ⟨⟨hbit, hlt⟩, hloop⟩ := h'
  have hz : x.testBit (A + t) = true := by
    have h1 := testBit_of_land hbit
    rwa [shiftRight_eq', Nat.testBit_shiftRight] at h1
  have hxW : x < 2 ^ W := by rw [hx]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hzW : A + t < W := testBit_lt_of_lt hxW hz
  intro k1 hk1 a a1 l1 k2 a2 ha hl1 hk2 h0 h1
  rcases Nat.lt_or_ge k1 (1 + (A + t - l0)) with hk | hk
  · exact k1Loop_sound hi hc0 hx hl0W _ 1 c0 hloop (by simpa using hc0) (Nat.le_refl 1) k1 hk1 hk
      a a1 l1 k2 a2 ha hl1 hk2 h0 h1
  · exfalso
    have hm := mod_eq_of_rel hc0 h0 (j := A + t + 1) (by omega) (by omega) (by omega)
    have hxm := x_mod (c0 := c0) (W := W) (j := A + t + 1) (l0 := l0) (by omega) (by omega)
    rw [← hxm, ← hx] at hm
    have e := congrArg (fun z => Nat.testBit z (A + t)) hm
    simp [Nat.testBit_mod_two_pow, testBit_small ha (Nat.le_add_right A t), hz] at e

theorem lLoop_succ (B E1 W i3 A A2 W2 k0 c0 cnt l0 : Nat) :
    lLoop B E1 W i3 A A2 W2 k0 c0 (cnt + 1) l0 =
      (lBody B E1 W i3 A A2 W2 k0 c0 l0 && lLoop B E1 W i3 A A2 W2 k0 c0 cnt (Nat.add l0 1)) := rfl

theorem lLoop_sound {B E1 W i3 A k0 c0 : Nat} (hi : 3 * i3 % 2 ^ W = 1)
    (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) : ∀ cnt l0,
    lLoop B E1 W i3 A (2 ^ A) (2 ^ W) k0 c0 cnt l0 = true → 1 ≤ l0 → l0 + cnt ≤ W + 1 →
      ∀ l0', l0 ≤ l0' → l0' < l0 + cnt → LCond B A k0 l0' := by
  intro cnt
  induction cnt with
  | zero => intro l0 _ _ _ l0' h1 h2; omega
  | succ cnt ih =>
    intro l0 h hl hW l0' h1 h2
    rw [lLoop_succ, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with he | hlt
    · subst he
      exact lBody_sound h.1 hi hc0 (by omega) hl
    · exact ih (l0 + 1) h.2 (by omega) (by omega) l0' hlt (by omega)

/-- **Soundness of `kOK3`.** -/
theorem kOK3_sound {N B E1 W i3 k0 c0 : Nat} (h : kOK3 N B E1 W i3 k0 c0 = true)
    (hi : 3 * i3 % 2 ^ W = 1) (hc0 : 3 ^ k0 * c0 % 2 ^ W = 1) (hc0W : c0 < 2 ^ W)
    (hkN : k0 ≤ N) : TripleCond N B k0 := by
  obtain ⟨A, hA⟩ : ∃ A, A = cond (Nat.blt k0 N) (Nat.sub N k0) 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = lowScan (c0 >>> A) W 0 := ⟨_, rfl⟩
  have h' : kCore3 B E1 W i3 k0 c0 A t = true := by rw [ht, hA]; exact h
  simp only [kCore3, Bool.and_eq_true, Nat.beq_eq] at h'
  obtain ⟨hbit, hloop⟩ := h'
  have hz : c0.testBit (A + t) = true := by
    have h1 := testBit_of_land hbit
    rwa [shiftRight_eq', Nat.testBit_shiftRight] at h1
  have hzW : A + t < W := testBit_lt_of_lt hc0W hz
  intro a l0 k1 a1 l1 k2 a2 ha hN hl0 hk1 hl1 hk2 h0 h1
  have haA : a < 2 ^ A := by rw [hA]; exact a_lt ha hN hkN
  rcases Nat.lt_or_ge (A + t) l0 with hlt | hle
  · exact (bit_false hc0 h0 hc0W hz (Nat.le_add_right A t) hlt haA).elim
  · exact lLoop_sound hi hc0 _ 1 hloop (Nat.le_refl 1) (by simp only [Nat.add_eq]; omega) l0 hl0
      (by simp only [Nat.add_eq]; omega) k1 hk1 a a1 l1 k2 a2 haA hl1 hk2 h0 h1

theorem loop3_succ (N B E1 W i3 cnt k c : Nat) : loop3 N B E1 W i3 (cnt + 1) k c =
    (kOK3 N B E1 W i3 k (Nat.mod (Nat.mul c i3) (Nat.pow 2 W)) &&
      loop3 N B E1 W i3 cnt (Nat.add k 1) (Nat.mod (Nat.mul c i3) (Nat.pow 2 W))) := rfl

/-- `TripleCond` for every `k₀ ∈ [lo, hi)` with `k₀ ≤ N`. -/
def RangeCond3 (N B lo hi : Nat) : Prop :=
  ∀ k0, lo ≤ k0 → k0 < hi → k0 ≤ N → TripleCond N B k0

theorem loop3_sound {N B E1 W i3 : Nat} (hi : 3 * i3 % 2 ^ W = 1) : ∀ cnt k c,
    loop3 N B E1 W i3 cnt k c = true → 3 ^ (k - 1) * c % 2 ^ W = 1 → 1 ≤ k →
      RangeCond3 N B k (k + cnt) := by
  intro cnt
  induction cnt with
  | zero => intro k c _ _ _ k0 h1 h2; omega
  | succ cnt ih =>
    intro k c h hc hk k0 h1 h2 hkN
    rw [loop3_succ, Bool.and_eq_true] at h
    have hc' := inv_step hc hi hk
    rcases Nat.eq_or_lt_of_le h1 with he | hlt
    · subst he
      exact kOK3_sound h.1 hi hc' (Nat.mod_lt _ (Nat.two_pow_pos W)) hkN
    · exact ih (k + 1) _ h.2 (by rw [Nat.add_sub_cancel]; exact hc') (by omega) k0 hlt (by omega)
        hkN

/-- **Soundness of the chunk checker.** -/
theorem rangeOK3_sound {N B E1 W i3 k c0 cnt : Nat} (h : rangeOK3 N B E1 W i3 k c0 cnt = true) :
    RangeCond3 N B k (k + cnt) := by
  simp only [rangeOK3, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hk, hi⟩, hc⟩, hl⟩ := h
  exact loop3_sound hi cnt k c0 hl hc hk

theorem RangeCond3.trans {N B a b c : Nat} (h1 : RangeCond3 N B a b) (h2 : RangeCond3 N B b c) :
    RangeCond3 N B a c := by
  intro k0 ha hc hkN
  rcases Nat.lt_or_ge k0 b with hb | hb
  · exact h1 k0 ha hb hkN
  · exact h2 k0 hb hc hkN

/-- The three-rise bound for all first rises `1 ≤ k₀ ≤ N`. -/
def AllTriples (N B : Nat) : Prop := ∀ k0, 1 ≤ k0 → k0 ≤ N → TripleCond N B k0

theorem allTriples_of_range {N B : Nat} (h : RangeCond3 N B 1 (N + 1)) : AllTriples N B :=
  fun k0 h1 h2 => h k0 h1 (by omega) h2

end Collatz.ThreeRise
