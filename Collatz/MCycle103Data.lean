import Collatz.MCycle103Certs5

/-!
# No Collatz 103-cycle when every `n ≤ 2⁷¹` reaches 1

`data103` is in `MCycle103Def.lean`. Its walk is evaluated in pieces in `MCycle103Walk1..11`
(`WalkSplit.lean`) and the certificates of the listed shapes in `MCycle103Certs1..5`;
`data103_ok` assembles them into Alick's `mOK` check.
-/

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs103 : certsOK 103 20 grid103 data103.certs shapes103 = true := by
  rw [shapes103_split]
  simp only [certsOK_append, certs103_0, certs103_1, certs103_2, certs103_3, certs103_4, certs103_5, certs103_6, certs103_7, certs103_8, certs103_9, certs103_10, certs103_11, certs103_12, certs103_13, certs103_14, certs103_15, certs103_16, certs103_17, certs103_18, certs103_19, Bool.and_self]

theorem data103_ok : mOK 103 20 grid103 data103 = true := by
  unfold mOK
  rw [data103_shapes, certs103, Bool.and_true]
  decide +kernel

/-- **No Collatz 103-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_103_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 103 := fun hm =>
  mOK_sound hR grid103_ok (by norm_num) data103_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
