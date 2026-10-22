import Collatz.MCycle104Certs8

/-!
# No Collatz 104-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data104` is in `MCycle104Def.lean`; its walk is evaluated in `MCycle104Walk1..19` and the
certificates in `MCycle104Certs1..8`; `data104_ok` assembles them into `mOK3`.
-/

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs104 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104 = true := by
  rw [shapes104_split]
  simp only [certsOK3_append, certs104_0, certs104_1, certs104_2, certs104_3, certs104_4, certs104_5, certs104_6, certs104_7, certs104_8, certs104_9, certs104_10, certs104_11, certs104_12, certs104_13, certs104_14, certs104_15, certs104_16, certs104_17, certs104_18, certs104_19, certs104_20, certs104_21, certs104_22, certs104_23, certs104_24, certs104_25, certs104_26, certs104_27, certs104_28, certs104_29, certs104_30, Bool.and_self]

theorem data104_ok : mOK3 104 20 grid103 grid3_105 data104 = true := by
  unfold mOK3
  rw [data104_shapes, certs104, Bool.and_true]
  decide +kernel

/-- **No Collatz 104-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_104_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 104 := fun hm =>
  mOK3_sound hR grid103_ok grid3_105_ok (by norm_num) data104_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
