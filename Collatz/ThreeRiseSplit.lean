import Collatz.ThreeRiseCheck

/-!
# The three-rise checker split over `ℓ₀` (one first rise `k₀` in several kernel checks)

`rangeOK3` checks whole first rises `k₀`; for large `N` one `k₀` has up to `N²/2` triples, more than
one `decide +kernel` should hold in memory. `lRangeOK3` checks the triples of one `k₀` with
`ℓ₀ ∈ [l, l + cnt)` (the same `lLoop` as `kOK3`), `LRange3.trans` joins the pieces, and
`tripleCond_of_lRange` closes `k₀` once the pieces reach a set bit `hi − 1 ≥ A` of `c₀ = 3^{−k₀}`
(`kTail3`; every `ℓ₀ ≥ hi` is impossible by `TwoRise.bit_false`), exactly as in `kOK3_sound`.
-/

namespace Collatz.ThreeRise

open Collatz.TwoRise

/-- `A` for the first rise `k₀` below `2^N` (as in `kOK3`). -/
def aOf (N k0 : Nat) : Nat := cond (Nat.blt k0 N) (Nat.sub N k0) 1

/-- The bound for first rise `k₀` and every `ℓ₀ ∈ [lo, hi)`. -/
def LRange3 (N B k0 lo hi : Nat) : Prop :=
  ∀ l0, lo ≤ l0 → l0 < hi → LCond B (aOf N k0) k0 l0

/-- The checker for first rise `k₀` and `ℓ₀ ∈ [l, l + cnt)`, `c₀ = 3^{−k₀} mod 2^W`. -/
def lRangeOK3 (N B E1 W i3 k0 c0 l cnt : Nat) : Bool :=
  Nat.ble 1 l && Nat.ble (Nat.add l cnt) (Nat.add W 1) &&
    Nat.beq (Nat.mod (Nat.mul 3 i3) (Nat.pow 2 W)) 1 &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 k0) c0) (Nat.pow 2 W)) 1 &&
    lLoop B E1 W i3 (aOf N k0) (Nat.pow 2 (aOf N k0)) (Nat.pow 2 W) k0 c0 cnt l

theorem lRangeOK3_sound {N B E1 W i3 k0 c0 l cnt : Nat}
    (h : lRangeOK3 N B E1 W i3 k0 c0 l cnt = true) : LRange3 N B k0 l (l + cnt) := by
  simp only [lRangeOK3, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, hW⟩, hi⟩, hc⟩, hl⟩ := h
  intro l0 ha hb
  exact lLoop_sound hi hc cnt l hl h1 hW l0 ha hb

theorem LRange3.trans {N B k0 a b c : Nat} (h1 : LRange3 N B k0 a b) (h2 : LRange3 N B k0 b c) :
    LRange3 N B k0 a c := by
  intro l0 ha hc
  rcases Nat.lt_or_ge l0 b with hb | hb
  · exact h1 l0 ha hb
  · exact h2 l0 hb hc

/-- The closing test for `k₀`: `c₀ = 3^{−k₀} mod 2^W` and bit `hi − 1 ≥ A` of `c₀` is set. -/
def kTail3 (N W k0 c0 hi : Nat) : Bool :=
  Nat.ble k0 N && Nat.blt c0 (Nat.pow 2 W) &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 k0) c0) (Nat.pow 2 W)) 1 &&
    Nat.ble (Nat.add (aOf N k0) 1) hi &&
    Nat.beq (Nat.land (Nat.shiftRight c0 (Nat.sub hi 1)) 1) 1

theorem tripleCond_of_lRange {N B W k0 c0 hi : Nat} (ht : kTail3 N W k0 c0 hi = true)
    (hr : LRange3 N B k0 1 hi) : TripleCond N B k0 := by
  simp only [kTail3, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at ht
  obtain ⟨⟨⟨⟨hkN, hc0W⟩, hc0⟩, hA⟩, hbit⟩ := ht
  have hz : c0.testBit (hi - 1) = true := testBit_of_land hbit
  have hA' : aOf N k0 + 1 ≤ hi := hA
  intro a l0 k1 a1 l1 k2 a2 ha hN hl0 hk1 hl1 hk2 h0 h1
  have haA : a < 2 ^ aOf N k0 := a_lt ha hN hkN
  rcases Nat.lt_or_ge (hi - 1) l0 with hlt | hle
  · exact (bit_false hc0 h0 hc0W hz (by omega) hlt haA).elim
  · exact hr l0 hl0 (by omega) k1 hk1 a a1 l1 k2 a2 haA hl1 hk2 h0 h1

theorem rangeCond3_single {N B k0 : Nat} (h : TripleCond N B k0) : RangeCond3 N B k0 (k0 + 1) := by
  intro k h1 h2 _
  obtain rfl : k = k0 := by omega
  exact h

end Collatz.ThreeRise
