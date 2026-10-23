import Collatz.TwoRiseCheck
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# A linear-time two-rise checker (`AllPairs N B` for large `N`)

`TwoRise.rangeOK` spends almost all of its kernel time in the direct test `directOK`: a product of
the `W`-bit number `c = 3^{−k₀} mod 2^W` by a `j`-bit number and a division by `2^j`, run at every
candidate `ℓ` of the 16-bit window search (about `A / 4096` false candidates per first rise, plus
`A / (2 · 3^{k₀−1})` true periodic matches for `k₀ ≤ 6`), so a first rise costs `Θ(N²)` and
`AllPairs N B` costs `Θ(N³)`. This file checks the same `PairCond N B k₀` with the same window
search (`TwoRise.matchMask`) but with only linear-time kernel operations:

* `dOK`: the direct test at `ℓ`, as `(c mod 2^j + 2^j − (c mod 2^d) 2^ℓ) mod 2^j ≥ 2^A` with masks and
  shifts (`j = d + ℓ`, `d = B + 1 − k₀`); `dOK_sound` turns it into `TwoRise.directOK`;
* the candidates of the window search carry their exponent (found by bisection and verified);
* the first rises `k₀` with `3^{k₀} 2^N ≤ 2^{B+2} − 2^{k₀+1}` are closed by size (`smallOK`): there
  `k₀ + k₁ ≤ B` holds for every odd `n < 2^N`;
* the loop runs downwards, `c ↦ 3c mod 2^W` (an add, a shift and a mask), from a start value
  found by repeated squaring and verified (`rangeOK2`).

Soundness reuses the 2-adic lemmas of `Collatz.TwoRise` (`directOK_false`, `bit_false`,
`window_borrow`, `testBit_matchMask`, `high_bits_of_pred`).
-/

namespace Collatz.TwoRise2

open Collatz.TwoRise

/-! ### Linear-time building blocks -/

/-- `2^e`, built by a shift. -/
def p2 (e : Nat) : Nat := Nat.shiftLeft 1 e

theorem p2_eq (e : Nat) : p2 e = 2 ^ e := by
  show 1 <<< e = 2 ^ e
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-- `x mod 2^e`, as a mask. -/
def lo (x e : Nat) : Nat := Nat.land x (Nat.sub (p2 e) 1)

theorem lo_eq (x e : Nat) : lo x e = x % 2 ^ e := by
  unfold lo
  rw [p2_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x e

/-! ### The direct test -/

/-- The direct test at `ℓ = l` for `d = B + 1 − k₀` and `cd = c mod 2^d`: with `j = d + l`, `j ≤ W`
and `(c mod 2^j + 2^j − cd · 2^l) mod 2^j ≥ 2^A`, i.e. `γ = c (1 − 2^ℓ)` has a set bit in `[A, j)`. -/
def dOK (d A W c cd l : Nat) : Bool :=
  Nat.ble (Nat.add d l) W &&
    Nat.ble (p2 A)
      (lo (Nat.sub (Nat.add (lo c (Nat.add d l)) (p2 (Nat.add d l))) (Nat.shiftLeft cd l)) (Nat.add d l))

/-- The value of the linear-time test equals the value of `directOK`. -/
theorem val_eq (c d l : Nat) :
    c * (2 ^ (d + l) + 1 - 2 ^ l) % 2 ^ (d + l) =
      (c % 2 ^ (d + l) + 2 ^ (d + l) - c % 2 ^ d * 2 ^ l) % 2 ^ (d + l) := by
  have hJ : 2 ^ (d + l) = 2 ^ d * 2 ^ l := Nat.pow_add 2 d l
  have hLJ : 2 ^ l ≤ 2 ^ (d + l) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left l d)
  have hcd : c % 2 ^ d * 2 ^ l < 2 ^ (d + l) := by
    rw [hJ]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.two_pow_pos l)
  apply nat_mod_eq_of_int_dvd
  have e1 := Nat.div_add_mod c (2 ^ (d + l))
  have e2 := Nat.div_add_mod c (2 ^ d)
  refine ⟨(c : Int) + ((c / 2 ^ (d + l) : Nat) : Int) - ((c / 2 ^ d : Nat) : Int) - 1, ?_⟩
  have i1 : ((2 ^ (d + l) * (c / 2 ^ (d + l)) + c % 2 ^ (d + l) : Nat) : Int) = (c : Int) := by
    rw [e1]
  have i2 : ((2 ^ d * (c / 2 ^ d) + c % 2 ^ d : Nat) : Int) = (c : Int) := by rw [e2]
  have i3 : ((2 ^ (d + l) : Nat) : Int) = ((2 ^ d : Nat) : Int) * ((2 ^ l : Nat) : Int) := by
    rw [hJ, Int.natCast_mul]
  push_cast at i1 i2 i3
  rw [Int.natCast_mul, Int.ofNat_sub (by omega), Int.ofNat_sub (by omega)]
  push_cast
  linear_combination -i1 + (2 : Int) ^ l * i2 + ((c / 2 ^ d : Nat) : Int) * i3

/-- **The linear-time direct test implies the old one.** -/
theorem dOK_sound {d A W c l : Nat} (h : dOK d A W c (c % 2 ^ d) l = true) :
    directOK (2 ^ d) (2 ^ A) (2 ^ W) c (2 ^ l) = true := by
  unfold dOK at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨hj, hv⟩ := h
  simp only [lo_eq, p2_eq, Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hj hv
  rw [directOK_iff, ← Nat.pow_add]
  exact ⟨Nat.pow_le_pow_right (by decide) hj, by rw [val_eq]; exact hv⟩

/-- `dOK` at `l, l + 1, …, l + cnt − 1`. -/
def dRange (d A W c cd cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih l => dOK d A W c cd l && ih (Nat.add l 1)) cnt

theorem dRange_sound {d A W c cd : Nat} : ∀ (cnt l : Nat), dRange d A W c cd cnt l = true →
    ∀ q < cnt, dOK d A W c cd (l + q) = true := by
  intro cnt
  induction cnt with
  | zero => intro l _ q hq; omega
  | succ cnt ih =>
    intro l h q hq
    have h' : (dOK d A W c cd l && dRange d A W c cd cnt (Nat.add l 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases q with _ | q
    · simpa using h'.1
    · have := ih _ h'.2 q (by omega)
      rwa [show Nat.add l 1 + q = l + (q + 1) by rw [Nat.add_eq]; omega] at this

/-! ### Candidates with their exponents -/

/-- A guess for `i` with `x = 2^i` (bisection on `[lo, hi)`, fuel `f`); only a heuristic. -/
def lg (x f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => cond (Nat.ble hi (Nat.add lo 1)) lo
      (cond (Nat.beq (Nat.shiftRight x (Nat.shiftRight (Nat.add lo hi) 1)) 0)
        (ih lo (Nat.shiftRight (Nat.add lo hi) 1)) (ih (Nat.shiftRight (Nat.add lo hi) 1) hi))) f

/-- `dOK` at `ℓ = A − i` for every set bit `i` of `mm` (`i ≤ A`); fuel `f`, bisection bound `U`. -/
def fb (d A W c cd U f : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun mm => Nat.beq mm 0)
    (fun _ ih mm => cond (Nat.beq mm 0) true
      (let Pt := Nat.land mm (Nat.xor mm (Nat.sub mm 1));
        let i := lg Pt 40 0 U;
        Nat.beq (p2 i) Pt && Nat.beq (Nat.land mm Pt) Pt && Nat.ble i A &&
          dOK d A W c cd (Nat.sub A i) && ih (Nat.xor mm Pt))) f

theorem fb_zero (d A W c cd U mm : Nat) : fb d A W c cd U 0 mm = Nat.beq mm 0 := rfl

theorem fb_succ (d A W c cd U f mm : Nat) : fb d A W c cd U (f + 1) mm =
    cond (Nat.beq mm 0) true
      (Nat.beq (p2 (lg (Nat.land mm (Nat.xor mm (Nat.sub mm 1))) 40 0 U))
          (Nat.land mm (Nat.xor mm (Nat.sub mm 1))) &&
        Nat.beq (Nat.land mm (Nat.land mm (Nat.xor mm (Nat.sub mm 1))))
          (Nat.land mm (Nat.xor mm (Nat.sub mm 1))) &&
        Nat.ble (lg (Nat.land mm (Nat.xor mm (Nat.sub mm 1))) 40 0 U) A &&
        dOK d A W c cd (Nat.sub A (lg (Nat.land mm (Nat.xor mm (Nat.sub mm 1))) 40 0 U)) &&
        fb d A W c cd U f (Nat.xor mm (Nat.land mm (Nat.xor mm (Nat.sub mm 1))))) := rfl

/-- Every set bit `i` of `mm` has `i ≤ A` and passed `dOK` at `ℓ = A − i`. -/
theorem fb_sound {d A W c cd U : Nat} : ∀ (f mm : Nat), fb d A W c cd U f mm = true →
    ∀ i, mm.testBit i = true → i ≤ A ∧ dOK d A W c cd (A - i) = true := by
  intro f
  induction f with
  | zero =>
    intro mm h i hi
    rw [fb_zero, Nat.beq_eq] at h
    subst h
    simp at hi
  | succ f ih =>
    intro mm h i hi
    rw [fb_succ] at h
    by_cases h0 : mm = 0
    · subst h0; simp at hi
    · have hb : Nat.beq mm 0 = false := by
        cases hq : Nat.beq mm 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h0
      rw [hb] at h
      simp only [Bool.cond_false, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
      generalize Nat.land mm (Nat.xor mm (Nat.sub mm 1)) = Pt at h
      generalize lg Pt 40 0 U = t at h
      obtain ⟨⟨⟨⟨h1, h3⟩, hA⟩, h4⟩, h5⟩ := h
      rw [p2_eq] at h1
      subst h1
      have hmt : mm.testBit t = true := by
        have e := congrArg (fun x => Nat.testBit x t) h3
        simp only [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at e
        exact e
      by_cases hit : i = t
      · subst hit; exact ⟨hA, by simpa [Nat.sub_eq] using h4⟩
      · apply ih _ h5 i
        rw [Nat.xor_eq, Nat.testBit_xor, hi, Nat.testBit_two_pow]
        simp [Ne.symm hit]

/-! ### The pattern test -/

/-- `TwoRise.patternCore` with the candidates checked by `fb`. -/
def patCore2 (d A W c cd E1 L M X P s : Nat) : Bool :=
  cond (Nat.blt s E1)
    (Nat.beq (Nat.land (Nat.shiftRight P s) 1) 1 && Nat.beq (Nat.mod P (Nat.pow 2 s)) 0 &&
      fb d A W c cd W L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)))
    (Nat.beq P 0 && fb d A W c cd W L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)))

/-- `patCore2` for `ℓ ∈ [lmin, A − 1]` with its intermediate values (masks, no divisions). -/
def patOK2 (d A W c cd E1 lmin : Nat) : Bool :=
  let L := Nat.add (Nat.sub A lmin) 1
  let P := lo (Nat.shiftRight c A) E1
  patCore2 d A W c cd E1 L (Nat.sub (p2 L) 1) (lo c (Nat.add A E1)) P (lowScan P E1 0)

theorem patCore2_zero_false {d A W c cd E1 L M X P s : Nat}
    (h : patCore2 d A W c cd E1 L M X P s = true) (hs : E1 ≤ s) :
    P = 0 ∧ fb d A W c cd W L
      (Nat.land (Nat.lor (matchMask M E1 X 0) (matchMask M E1 X (Nat.sub (Nat.pow 2 E1) 1)))
        (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = false := by
    rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega
  simp only [patCore2, hb, Bool.cond_false, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem patCore2_lt {d A W c cd E1 L M X P s : Nat}
    (h : patCore2 d A W c cd E1 L M X P s = true) (hs : s < E1) :
    P.testBit s = true ∧ P % 2 ^ s = 0 ∧ fb d A W c cd W L
        (Nat.land (matchMask M (Nat.sub E1 (Nat.add s 1)) (Nat.shiftRight X (Nat.add s 1))
          (Nat.shiftRight P (Nat.add s 1))) (Nat.xor M 1)) = true := by
  have hb : Nat.blt s E1 = true := by rw [Nat.blt_eq]; exact hs
  simp only [patCore2, hb, Bool.cond_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, by rw [mod_eq', pow_eq'] at h2; exact h2, h3⟩
  rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h1
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  simp [h1]

/-- **The pattern test.** If the window of `c` at `i ∈ [1, L − 1]` (`i ≤ A`) is `P` or `P − 1`,
`dOK` has been run and passed at `ℓ = A − i`. -/
theorem patCore2_sound {d A W c cd E1 L P s i : Nat}
    (h : patCore2 d A W c cd E1 L (2 ^ L - 1) (c % 2 ^ (A + E1)) P s = true)
    (hi1 : 1 ≤ i) (hiL : i < L) (hiA : i ≤ A)
    (hw : (c >>> i) % 2 ^ E1 = P ∨ ((c >>> i) % 2 ^ E1 + 1) % 2 ^ E1 = P) :
    dOK d A W c cd (A - i) = true := by
  have hmask : ((2 ^ L - 1) ^^^ 1).testBit i = true := testBit_xor_one_mask hi1 hiL
  have hX : ∀ j, j < E1 → (c % 2 ^ (A + E1)).testBit (i + j) = c.testBit (i + j) := by
    intro j hj
    rw [Nat.testBit_mod_two_pow]
    have : i + j < A + E1 := by omega
    simp [this]
  have hwlt : (c >>> i) % 2 ^ E1 < 2 ^ E1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases Nat.lt_or_ge s E1 with hs | hs
  · obtain ⟨hPs, hPs0, hf⟩ := patCore2_lt h hs
    simp only [Nat.land_eq, Nat.xor_eq, Nat.sub_eq, Nat.add_eq, shiftRight_eq'] at hf
    refine (fb_sound _ _ hf i ?_).2
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
  · obtain ⟨hP0, hf⟩ := patCore2_zero_false h hs
    subst hP0
    simp only [Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.sub_eq, pow_eq'] at hf
    refine (fb_sound _ _ hf i ?_).2
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

/-! ### One first rise -/

/-- All tests for one `k₀`: `A = N − k₀` (`1` if `k₀ = N`), `d = B + 1 − k₀`, `cd = c mod 2^d`,
`y = c >>> A` and `t` (claimed) a set bit of `y`. -/
def kCore2 (B E1 W k0 c A d cd y t lmin : Nat) : Bool :=
  Nat.ble k0 (Nat.add B 1) && Nat.beq (Nat.land (Nat.shiftRight y t) 1) 1 &&
    dRange d A W c cd (Nat.add t 1) A &&
    dRange d A W c cd (Nat.sub (Nat.min A lmin) 1) 1 &&
    cond (Nat.ble A lmin) true (Nat.ble (Nat.add A E1) W && patOK2 d A W c cd E1 lmin)

/-- The size test `3^{k₀} 2^N ≤ 2^{B+2} − 2^{k₀+1}` (only tried for `k₀ ≤ 64`). -/
def smallOK (N B k0 : Nat) : Bool :=
  Nat.ble k0 64 &&
    Nat.ble (Nat.mul (Nat.pow 3 k0) (p2 N)) (Nat.sub (p2 (Nat.add B 2)) (p2 (Nat.add k0 1)))

/-- The test for one first rise `k₀` (`c = 3^{−k₀} mod 2^W`). -/
def kOK2 (N B E1 W k0 c : Nat) : Bool :=
  smallOK N B k0 ||
    (let A := cond (Nat.blt k0 N) (Nat.sub N k0) 1
     let d := Nat.sub (Nat.add B 1) k0
     let y := Nat.shiftRight c A
     kCore2 B E1 W k0 c A d (lo c d) y (lowScan y W 0)
       (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1))))

/-- **The size test is sound**: `2^ℓ 2^{B+1} + 2^{k₀} ≤ 3^{k₀} 2^N + 2^{k₀} 2^ℓ` would follow from
`k₀ + k₁ > B`, and `ℓ ≥ 1` contradicts it. -/
theorem smallOK_sound {N B k0 : Nat} (h : smallOK N B k0 = true) :
    PairCond N B k0 := by
  unfold smallOK at h
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨_, h⟩ := h
  simp only [p2_eq, Nat.mul_eq, pow_eq', Nat.add_eq, Nat.sub_eq] at h
  intro a l k1 a' ha hN hl hrel
  apply Nat.le_of_not_lt
  intro hbad
  have hX : 2 ≤ 2 ^ l := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hl
    simpa using this
  have ha' : 1 ≤ a' := by
    rcases Nat.eq_zero_or_pos a' with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hrel
      omega
    · exact h0
  have h1 : 2 ^ (l + k1) + 1 ≤ 3 ^ k0 * a + 2 ^ l := by
    have : 2 ^ (l + k1) ≤ 2 ^ (l + k1) * a' := Nat.le_mul_of_pos_right _ ha'
    omega
  have h3 : 2 ^ l * 2 ^ (B + 1) ≤ 2 ^ k0 * 2 ^ (l + k1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hQ : 1 ≤ 2 ^ k0 := Nat.one_le_two_pow
  have e2 : 2 ^ (B + 2) = 2 * 2 ^ (B + 1) := by
    rw [show B + 2 = B + 1 + 1 by omega, Nat.pow_succ]; omega
  have e3 : 2 ^ (k0 + 1) = 2 * 2 ^ k0 := by rw [Nat.pow_succ]; omega
  rw [e2, e3] at h
  have h5 : 3 ^ k0 * (2 ^ k0 * a) ≤ 3 ^ k0 * 2 ^ N := Nat.mul_le_mul_left _ hN
  have h6 : 2 ^ k0 * (2 ^ (l + k1) + 1) ≤ 2 ^ k0 * (3 ^ k0 * a + 2 ^ l) := Nat.mul_le_mul_left _ h1
  have hpos : 1 ≤ 3 ^ k0 * 2 ^ N := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.two_pow_pos _)
  generalize 2 ^ l = X at *
  generalize 2 ^ (B + 1) = P at *
  generalize 2 ^ k0 = Q at *
  generalize 2 ^ (l + k1) = Y at *
  generalize 3 ^ k0 = R at *
  generalize 2 ^ N = M at *
  -- `X P ≤ Q Y`, `Q Y + Q ≤ R (Q a) + Q X ≤ R M + Q X`, `R M ≤ 2P − 2Q`, `X ≥ 2`, `Q ≥ 1`
  have hRM : R * M + 2 * Q ≤ 2 * P := by omega
  have hPQ : Q ≤ P := by omega
  obtain ⟨Z, rfl⟩ := Nat.exists_eq_add_of_le hPQ
  have hZ : 2 * Z ≤ X * Z := Nat.mul_le_mul_right Z hX
  nlinarith [hZ]

theorem kCore2_facts {B E1 W k0 c A d cd y t lmin : Nat}
    (h : kCore2 B E1 W k0 c A d cd y t lmin = true) :
    k0 ≤ B + 1 ∧ (y >>> t) % 2 = 1 ∧ dRange d A W c cd (t + 1) A = true ∧
      dRange d A W c cd (min A lmin - 1) 1 = true ∧
      (lmin < A → A + E1 ≤ W ∧ patOK2 d A W c cd E1 lmin = true) := by
  simp only [kCore2, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, h3, ?_, ?_⟩
  · rw [Nat.land_eq, shiftRight_eq', Nat.and_one_is_mod] at h2; exact h2
  · have : Nat.min A lmin = min A lmin := rfl
    rw [this] at h4; exact h4
  · intro hlt
    have hb : Nat.ble A lmin = false := by
      rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega
    rw [hb, Bool.cond_false, Bool.and_eq_true, Nat.ble_eq] at h5
    exact h5

/-- **Soundness of the test for one `k₀`.** -/
theorem kCore2_sound {N B E1 W k0 c A d y t lmin : Nat}
    (h : kCore2 B E1 W k0 c A d (c % 2 ^ d) y t lmin = true)
    (hA : A = cond (Nat.blt k0 N) (Nat.sub N k0) 1) (hd : d = B + 1 - k0) (hy : y = c >>> A)
    (hlmin : lmin = max 1 (N + E1 - (B + 1)))
    (hc : 3 ^ k0 * c % 2 ^ W = 1) (hcW : c < 2 ^ W) (hkN : k0 ≤ N) :
    PairCond N B k0 := by
  intro a l k1 a' ha hN hl hrel
  apply Nat.le_of_not_lt
  intro hbad
  obtain ⟨_, hbit, hdr1, hdr2, hpat⟩ := kCore2_facts h
  have haA : a < 2 ^ A := by rw [hA]; exact a_lt ha hN hkN
  have hz : c.testBit (A + t) = true := by
    have h1 : (c >>> A).testBit t = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, ← hy]; simp [hbit]
    rwa [Nat.testBit_shiftRight] at h1
  have hbad' : B + 1 ≤ k0 + k1 := hbad
  have fin : dOK d A W c (c % 2 ^ d) l = true → False := by
    intro hq
    have := dOK_sound hq
    rw [hd] at this
    exact directOK_false this hc hrel rfl rfl rfl rfl hbad' haA
  rcases Nat.lt_or_ge (A + t) l with hlt | hge
  · exact bit_false hc hrel hcW hz (Nat.le_add_right A t) hlt haA
  rcases Nat.lt_or_ge l A with hlA | hAl
  · rcases Nat.lt_or_ge l lmin with hll | hll
    · have hq := dRange_sound _ _ hdr2 (l - 1) (by omega)
      rw [show 1 + (l - 1) = l by omega] at hq
      exact fin hq
    · obtain ⟨hAE, hp⟩ := hpat (by omega)
      have hkN' : k0 < N := by
        rcases Nat.lt_or_ge k0 N with h' | h'
        · exact h'
        · have hb : Nat.blt k0 N = false := by
            rw [Bool.eq_false_iff]; intro h''; rw [Nat.blt_eq] at h''; omega
          rw [hA, hb, Bool.cond_false] at hlA; omega
      have hAv : A = N - k0 := by
        have hb : Nat.blt k0 N = true := by rw [Nat.blt_eq]; exact hkN'
        rw [hA, hb, Bool.cond_true, Nat.sub_eq]
      have hwb := window_borrow (E := E1) hc hrel (Nat.le_of_lt hlA) hAE (by omega) haA
      simp only [patOK2, lo_eq, p2_eq, Nat.add_eq, Nat.sub_eq, shiftRight_eq'] at hp
      have hd' := patCore2_sound (A := A) (i := A - l) hp (by omega) (by omega)
        (Nat.sub_le A l) hwb
      rw [Nat.sub_sub_self (Nat.le_of_lt hlA)] at hd'
      exact fin hd'
  · have hq := dRange_sound _ _ hdr1 (l - A) (by omega)
    rw [Nat.add_sub_cancel' hAl] at hq
    exact fin hq

/-- **Soundness of `kOK2`.** -/
theorem kOK2_sound {N B E1 W k0 c : Nat} (h : kOK2 N B E1 W k0 c = true)
    (hc : 3 ^ k0 * c % 2 ^ W = 1) (hcW : c < 2 ^ W) (hkN : k0 ≤ N) : PairCond N B k0 := by
  unfold kOK2 at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact smallOK_sound h
  · have h' : kCore2 B E1 W k0 c (cond (Nat.blt k0 N) (Nat.sub N k0) 1) (Nat.sub (Nat.add B 1) k0)
        (c % 2 ^ (Nat.sub (Nat.add B 1) k0)) (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1))
        (lowScan (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1)) W 0)
        (Nat.max 1 (Nat.sub (Nat.add N E1) (Nat.add B 1))) = true := by
      rw [← lo_eq]; exact h
    exact kCore2_sound h' rfl rfl rfl rfl hc hcW hkN

/-! ### The downward loop and the chunk checker -/

/-- `k₀ = k, k − 1, …, k − cnt + 1`; on entry `c = 3^{−k} mod 2^W`; the update is `c ↦ 3c mod 2^W`. -/
def loop2 (N B E1 W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c => kOK2 N B E1 W k c && ih (Nat.sub k 1) (lo (Nat.add c (Nat.shiftLeft c 1)) W)) cnt

theorem loop2_succ (N B E1 W cnt k c : Nat) : loop2 N B E1 W (cnt + 1) k c =
    (kOK2 N B E1 W k c && loop2 N B E1 W cnt (Nat.sub k 1) (lo (Nat.add c (Nat.shiftLeft c 1)) W)) :=
  rfl

theorem step3 {k c W : Nat} (hc : 3 ^ k * c % 2 ^ W = 1) (hk : 1 ≤ k) :
    3 ^ (k - 1) * lo (Nat.add c (Nat.shiftLeft c 1)) W % 2 ^ W = 1 := by
  have e : Nat.add c (Nat.shiftLeft c 1) = 3 * c := by
    show c + c <<< 1 = 3 * c
    rw [Nat.shiftLeft_eq, Nat.pow_one]; omega
  have e3 : 3 ^ (k - 1) * 3 = 3 ^ k := by
    rw [← Nat.pow_succ]; congr 1; omega
  rw [lo_eq, e, Nat.mul_mod_mod, ← Nat.mul_assoc, e3, hc]

theorem loop2_sound {N B E1 W : Nat} : ∀ cnt k c,
    loop2 N B E1 W cnt k c = true → 3 ^ k * c % 2 ^ W = 1 → c < 2 ^ W → cnt ≤ k →
      RangeCond N B (k + 1 - cnt) (k + 1) := by
  intro cnt
  induction cnt with
  | zero => intro k c _ _ _ _ k0 h1 h2; omega
  | succ cnt ih =>
    intro k c h hc hcW hk k0 h1 h2 hkN
    rw [loop2_succ, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k0 k with hlt | hge
    · have hc' := step3 hc (by omega)
      have hcW' : lo (Nat.add c (Nat.shiftLeft c 1)) W < 2 ^ W := by
        rw [lo_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos W)
      have := ih (k - 1) _ h.2 hc' hcW' (by omega)
      exact this k0 (by omega) (by omega) hkN
    · obtain rfl : k0 = k := by omega
      exact kOK2_sound h.1 hc hcW hkN

/-- The checker for `k₀ ∈ [k + 1 − cnt, k]` (`cnt ≤ k`): `c₀ < 2^W` and `3^k c₀ ≡ 1 (mod 2^W)`, then
the downward loop. -/
def rangeOK2 (N B E1 W k cnt c0 : Nat) : Bool :=
  Nat.ble cnt k && Nat.blt c0 (p2 W) && Nat.beq (lo (Nat.mul (Nat.pow 3 k) c0) W) 1 &&
    loop2 N B E1 W cnt k c0

/-- **Soundness of the chunk checker.** -/
theorem rangeOK2_sound {N B E1 W k cnt c0 : Nat} (h : rangeOK2 N B E1 W k cnt c0 = true) :
    RangeCond N B (k + 1 - cnt) (k + 1) := by
  unfold rangeOK2 at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, lo_eq, p2_eq, Nat.mul_eq,
    pow_eq'] at h
  obtain ⟨⟨⟨hk, hW⟩, hc⟩, hl⟩ := h
  exact loop2_sound cnt k c0 hl hc hW hk

/-- `acc · b^e mod 2^W` by repeated squaring with fuel `f` (only produces a start value;
`rangeOK2` verifies it). -/
def powLo (W : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | f + 1, b, e, acc => cond (Nat.beq e 0) acc
      (powLo W f (lo (Nat.mul b b) W) (Nat.shiftRight e 1)
        (cond (Nat.beq (Nat.land e 1) 1) (lo (Nat.mul acc b) W) acc))

end Collatz.TwoRise2
