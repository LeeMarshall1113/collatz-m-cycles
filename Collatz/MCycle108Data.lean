import Collatz.MCycle108Certs47

/-!
# No Collatz 108-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data108` is in `MCycle108Def.lean`; its walk is evaluated in `MCycle108Walk1..57` and the
certificates in `MCycle108Certs1..47`; `data108_ok` assembles them into `mOK3`.
-/

set_option maxRecDepth 100000

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs108 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108 = true := by
  rw [shapes108_split]
  simp only [certsOK3_append, certs108_0, certs108_1, certs108_2, certs108_3, certs108_4, certs108_5, certs108_6, certs108_7, certs108_8, certs108_9, certs108_10, certs108_11, certs108_12, certs108_13, certs108_14, certs108_15, certs108_16, certs108_17, certs108_18, certs108_19, certs108_20, certs108_21, certs108_22, certs108_23, certs108_24, certs108_25, certs108_26, certs108_27, certs108_28, certs108_29, certs108_30, certs108_31, certs108_32, certs108_33, certs108_34, certs108_35, certs108_36, certs108_37, certs108_38, certs108_39, certs108_40, certs108_41, certs108_42, certs108_43, certs108_44, certs108_45, certs108_46, certs108_47, certs108_48, certs108_49, certs108_50, certs108_51, certs108_52, certs108_53, certs108_54, certs108_55, certs108_56, certs108_57, certs108_58, certs108_59, certs108_60, certs108_61, certs108_62, certs108_63, certs108_64, certs108_65, certs108_66, certs108_67, certs108_68, certs108_69, certs108_70, certs108_71, certs108_72, certs108_73, certs108_74, certs108_75, certs108_76, certs108_77, certs108_78, certs108_79, certs108_80, certs108_81, certs108_82, certs108_83, certs108_84, certs108_85, certs108_86, certs108_87, certs108_88, certs108_89, certs108_90, certs108_91, certs108_92, certs108_93, certs108_94, certs108_95, certs108_96, certs108_97, certs108_98, certs108_99, certs108_100, certs108_101, certs108_102, certs108_103, certs108_104, certs108_105, certs108_106, certs108_107, certs108_108, certs108_109, certs108_110, certs108_111, certs108_112, certs108_113, certs108_114, certs108_115, certs108_116, certs108_117, certs108_118, certs108_119, certs108_120, certs108_121, certs108_122, certs108_123, certs108_124, certs108_125, certs108_126, certs108_127, certs108_128, certs108_129, certs108_130, certs108_131, certs108_132, certs108_133, certs108_134, certs108_135, certs108_136, certs108_137, certs108_138, certs108_139, certs108_140, certs108_141, certs108_142, certs108_143, certs108_144, certs108_145, certs108_146, certs108_147, certs108_148, certs108_149, certs108_150, certs108_151, certs108_152, certs108_153, certs108_154, certs108_155, certs108_156, certs108_157, certs108_158, certs108_159, certs108_160, certs108_161, certs108_162, certs108_163, certs108_164, certs108_165, certs108_166, certs108_167, certs108_168, certs108_169, certs108_170, certs108_171, certs108_172, certs108_173, certs108_174, certs108_175, certs108_176, certs108_177, certs108_178, certs108_179, certs108_180, certs108_181, certs108_182, certs108_183, certs108_184, certs108_185, certs108_186, Bool.and_self]

theorem data108_ok : mOK3 108 20 grid108 grid3_107 data108 = true := by
  unfold mOK3
  rw [data108_shapes, certs108, Bool.and_true]
  decide +kernel

/-- **No Collatz 108-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_108_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 108 := fun hm =>
  mOK3_sound hR grid108_ok grid3_107_ok (by norm_num) data108_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
