import Collatz.MCycle106Certs7

/-!
# No Collatz 106-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data106` is in `MCycle106Def.lean`; its walk is evaluated in `MCycle106Walk1..19` and the
certificates in `MCycle106Certs1..7`; `data106_ok` assembles them into `mOK3`.
-/

set_option maxRecDepth 100000

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs106 : certsOK3 106 20 grid103 grid3_107 data106.certs shapes106 = true := by
  rw [shapes106_split]
  simp only [certsOK3_append, certs106_0, certs106_1, certs106_2, certs106_3, certs106_4, certs106_5, certs106_6, certs106_7, certs106_8, certs106_9, certs106_10, certs106_11, certs106_12, certs106_13, certs106_14, certs106_15, certs106_16, certs106_17, certs106_18, certs106_19, certs106_20, certs106_21, certs106_22, certs106_23, certs106_24, certs106_25, certs106_26, certs106_27, certs106_28, certs106_29, certs106_30, certs106_31, certs106_32, certs106_33, certs106_34, certs106_35, certs106_36, certs106_37, certs106_38, certs106_39, certs106_40, certs106_41, certs106_42, certs106_43, certs106_44, certs106_45, certs106_46, certs106_47, certs106_48, certs106_49, certs106_50, certs106_51, certs106_52, certs106_53, certs106_54, certs106_55, certs106_56, certs106_57, certs106_58, certs106_59, certs106_60, certs106_61, certs106_62, certs106_63, certs106_64, certs106_65, certs106_66, certs106_67, certs106_68, certs106_69, certs106_70, certs106_71, certs106_72, certs106_73, certs106_74, certs106_75, certs106_76, Bool.and_self]

theorem data106_ok : mOK3 106 20 grid103 grid3_107 data106 = true := by
  unfold mOK3
  rw [data106_shapes, certs106, Bool.and_true]
  decide +kernel

/-- **No Collatz 106-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_106_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 106 := fun hm =>
  mOK3_sound hR grid103_ok grid3_107_ok (by norm_num) data106_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
