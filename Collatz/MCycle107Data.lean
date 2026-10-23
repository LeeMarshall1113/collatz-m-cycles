import Collatz.MCycle107Certs10

/-!
# No Collatz 107-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data107` is in `MCycle107Def.lean`; its walk is evaluated in `MCycle107Walk1..32` and the
certificates in `MCycle107Certs1..10`; `data107_ok` assembles them into `mOK3`.
-/

set_option maxRecDepth 100000

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs107 : certsOK3 107 20 grid103 grid3_107 data107.certs shapes107 = true := by
  rw [shapes107_split]
  simp only [certsOK3_append, certs107_0, certs107_1, certs107_2, certs107_3, certs107_4, certs107_5, certs107_6, certs107_7, certs107_8, certs107_9, certs107_10, certs107_11, certs107_12, certs107_13, certs107_14, certs107_15, certs107_16, certs107_17, certs107_18, certs107_19, certs107_20, certs107_21, certs107_22, certs107_23, certs107_24, certs107_25, certs107_26, certs107_27, certs107_28, certs107_29, certs107_30, certs107_31, certs107_32, certs107_33, certs107_34, certs107_35, certs107_36, certs107_37, certs107_38, certs107_39, certs107_40, certs107_41, certs107_42, certs107_43, certs107_44, certs107_45, certs107_46, certs107_47, certs107_48, certs107_49, certs107_50, certs107_51, certs107_52, certs107_53, certs107_54, certs107_55, certs107_56, certs107_57, certs107_58, certs107_59, certs107_60, certs107_61, certs107_62, certs107_63, certs107_64, certs107_65, certs107_66, certs107_67, certs107_68, certs107_69, certs107_70, certs107_71, certs107_72, certs107_73, certs107_74, certs107_75, certs107_76, certs107_77, certs107_78, certs107_79, certs107_80, certs107_81, certs107_82, certs107_83, certs107_84, certs107_85, certs107_86, certs107_87, certs107_88, certs107_89, certs107_90, certs107_91, certs107_92, certs107_93, certs107_94, certs107_95, certs107_96, certs107_97, certs107_98, certs107_99, certs107_100, certs107_101, certs107_102, certs107_103, certs107_104, certs107_105, certs107_106, certs107_107, certs107_108, certs107_109, certs107_110, certs107_111, certs107_112, certs107_113, certs107_114, certs107_115, certs107_116, certs107_117, certs107_118, Bool.and_self]

theorem data107_ok : mOK3 107 20 grid103 grid3_107 data107 = true := by
  unfold mOK3
  rw [data107_shapes, certs107, Bool.and_true]
  decide +kernel

/-- **No Collatz 107-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_107_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 107 := fun hm =>
  mOK3_sound hR grid103_ok grid3_107_ok (by norm_num) data107_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
