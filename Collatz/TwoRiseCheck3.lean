import Collatz.TwoRiseCheck2

/-!
# `TwoRise2` with an adaptive window (heavy first rises)

In `TwoRise2.kOK2` the window search matches only the bits of `P = (c >>> A) mod 2^{E₁}` above its
lowest set bit `s` (the borrow ambiguity). When `s` is close to `E₁` almost nothing is matched, and
the search returns about `A / 2^{E₁ − s − 1}` candidates, each followed by a direct test. At
`N = 384012` a single such first rise (`s ≥ E₁ − 3`, probability about `2⁻²⁰` per rise) produced
tens of thousands of candidates in one declaration and took a module to 13 GB.

`kOK2x` therefore looks at `P` first: if its low `E₁ − D` bits vanish (`s ≥ E₁ − D`) it runs
`kOK2` with the wider window `E₂`, otherwise with `E₁`. Both branches are `kOK2`, so soundness is
`kOK2_sound` in each case; the loop and the chunk checker are those of `TwoRise2` with `kOK2x`.
-/

namespace Collatz.TwoRise2

open Collatz.TwoRise

/-- `kOK2` with window `E₂` when the low `E₁ − D` bits of the window at `A` vanish, else `E₁`. -/
def kOK2x (N B E1 E2 D W k0 c : Nat) : Bool :=
  cond (Nat.beq (lo (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1)) (Nat.sub E1 D)) 0)
    (kOK2 N B E2 W k0 c) (kOK2 N B E1 W k0 c)

theorem kOK2x_sound {N B E1 E2 D W k0 c : Nat} (h : kOK2x N B E1 E2 D W k0 c = true)
    (hc : 3 ^ k0 * c % 2 ^ W = 1) (hcW : c < 2 ^ W) (hkN : k0 ≤ N) : PairCond N B k0 := by
  unfold kOK2x at h
  cases hb : Nat.beq (lo (Nat.shiftRight c (cond (Nat.blt k0 N) (Nat.sub N k0) 1)) (Nat.sub E1 D)) 0
  · rw [hb, Bool.cond_false] at h; exact kOK2_sound h hc hcW hkN
  · rw [hb, Bool.cond_true] at h; exact kOK2_sound h hc hcW hkN

/-- `loop2` with `kOK2x`. -/
def loop2x (N B E1 E2 D W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c => kOK2x N B E1 E2 D W k c &&
      ih (Nat.sub k 1) (lo (Nat.add c (Nat.shiftLeft c 1)) W)) cnt

theorem loop2x_succ (N B E1 E2 D W cnt k c : Nat) : loop2x N B E1 E2 D W (cnt + 1) k c =
    (kOK2x N B E1 E2 D W k c &&
      loop2x N B E1 E2 D W cnt (Nat.sub k 1) (lo (Nat.add c (Nat.shiftLeft c 1)) W)) := rfl

theorem loop2x_sound {N B E1 E2 D W : Nat} : ∀ cnt k c,
    loop2x N B E1 E2 D W cnt k c = true → 3 ^ k * c % 2 ^ W = 1 → c < 2 ^ W → cnt ≤ k →
      RangeCond N B (k + 1 - cnt) (k + 1) := by
  intro cnt
  induction cnt with
  | zero => intro k c _ _ _ _ k0 h1 h2; omega
  | succ cnt ih =>
    intro k c h hc hcW hk k0 h1 h2 hkN
    rw [loop2x_succ, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k0 k with hlt | hge
    · have hc' := step3 hc (by omega)
      have hcW' : lo (Nat.add c (Nat.shiftLeft c 1)) W < 2 ^ W := by
        rw [lo_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos W)
      have := ih (k - 1) _ h.2 hc' hcW' (by omega)
      exact this k0 (by omega) (by omega) hkN
    · obtain rfl : k0 = k := by omega
      exact kOK2x_sound h.1 hc hcW hkN

/-- `rangeOK2` with `kOK2x`. -/
def rangeOK2x (N B E1 E2 D W k cnt c0 : Nat) : Bool :=
  Nat.ble cnt k && Nat.blt c0 (p2 W) && Nat.beq (lo (Nat.mul (Nat.pow 3 k) c0) W) 1 &&
    loop2x N B E1 E2 D W cnt k c0

theorem rangeOK2x_sound {N B E1 E2 D W k cnt c0 : Nat}
    (h : rangeOK2x N B E1 E2 D W k cnt c0 = true) : RangeCond N B (k + 1 - cnt) (k + 1) := by
  unfold rangeOK2x at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, lo_eq, p2_eq, Nat.mul_eq,
    pow_eq'] at h
  obtain ⟨⟨⟨hk, hW⟩, hc⟩, hl⟩ := h
  exact loop2x_sound cnt k c0 hl hc hW hk

end Collatz.TwoRise2
