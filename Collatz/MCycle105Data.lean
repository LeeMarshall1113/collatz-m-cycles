import Collatz.MCycle105Certs12

/-!
# No Collatz 105-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data105` is in `MCycle105Def.lean`; its walk is evaluated in `MCycle105Walk1..32` and the
certificates in `MCycle105Certs1..12`; `data105_ok` assembles them into `mOK3`.
-/

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs105 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105 = true := by
  rw [shapes105_split]
  simp only [certsOK3_append, certs105_0, certs105_1, certs105_2, certs105_3, certs105_4, certs105_5, certs105_6, certs105_7, certs105_8, certs105_9, certs105_10, certs105_11, certs105_12, certs105_13, certs105_14, certs105_15, certs105_16, certs105_17, certs105_18, certs105_19, certs105_20, certs105_21, certs105_22, certs105_23, certs105_24, certs105_25, certs105_26, certs105_27, certs105_28, certs105_29, certs105_30, certs105_31, certs105_32, certs105_33, certs105_34, certs105_35, certs105_36, certs105_37, certs105_38, certs105_39, certs105_40, certs105_41, certs105_42, certs105_43, certs105_44, certs105_45, certs105_46, Bool.and_self]

theorem data105_ok : mOK3 105 20 grid103 grid3_105 data105 = true := by
  unfold mOK3
  rw [data105_shapes, certs105, Bool.and_true]
  decide +kernel

/-- **No Collatz 105-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_105_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 105 := fun hm =>
  mOK3_sound hR grid103_ok grid3_105_ok (by norm_num) data105_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
