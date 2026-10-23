import Collatz.MCycle109Certs73

/-!
# No Collatz 109-cycle when every `n ≤ 2⁷¹` reaches 1 (three-rise chain)

`data109` is in `MCycle109Def.lean`; its walk is evaluated in `MCycle109Walk1..96` and the
certificates in `MCycle109Certs1..73`; `data109_ok` assembles them into `mOK3`.
-/

set_option maxRecDepth 100000

namespace Collatz

/-- The certificate check of all listed shapes, from the chunks. -/
theorem certs109 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109 = true := by
  rw [shapes109_split]
  simp only [certsOK3_append, certs109_0, certs109_1, certs109_2, certs109_3, certs109_4, certs109_5, certs109_6, certs109_7, certs109_8, certs109_9, certs109_10, certs109_11, certs109_12, certs109_13, certs109_14, certs109_15, certs109_16, certs109_17, certs109_18, certs109_19, certs109_20, certs109_21, certs109_22, certs109_23, certs109_24, certs109_25, certs109_26, certs109_27, certs109_28, certs109_29, certs109_30, certs109_31, certs109_32, certs109_33, certs109_34, certs109_35, certs109_36, certs109_37, certs109_38, certs109_39, certs109_40, certs109_41, certs109_42, certs109_43, certs109_44, certs109_45, certs109_46, certs109_47, certs109_48, certs109_49, certs109_50, certs109_51, certs109_52, certs109_53, certs109_54, certs109_55, certs109_56, certs109_57, certs109_58, certs109_59, certs109_60, certs109_61, certs109_62, certs109_63, certs109_64, certs109_65, certs109_66, certs109_67, certs109_68, certs109_69, certs109_70, certs109_71, certs109_72, certs109_73, certs109_74, certs109_75, certs109_76, certs109_77, certs109_78, certs109_79, certs109_80, certs109_81, certs109_82, certs109_83, certs109_84, certs109_85, certs109_86, certs109_87, certs109_88, certs109_89, certs109_90, certs109_91, certs109_92, certs109_93, certs109_94, certs109_95, certs109_96, certs109_97, certs109_98, certs109_99, certs109_100, certs109_101, certs109_102, certs109_103, certs109_104, certs109_105, certs109_106, certs109_107, certs109_108, certs109_109, certs109_110, certs109_111, certs109_112, certs109_113, certs109_114, certs109_115, certs109_116, certs109_117, certs109_118, certs109_119, certs109_120, certs109_121, certs109_122, certs109_123, certs109_124, certs109_125, certs109_126, certs109_127, certs109_128, certs109_129, certs109_130, certs109_131, certs109_132, certs109_133, certs109_134, certs109_135, certs109_136, certs109_137, certs109_138, certs109_139, certs109_140, certs109_141, certs109_142, certs109_143, certs109_144, certs109_145, certs109_146, certs109_147, certs109_148, certs109_149, certs109_150, certs109_151, certs109_152, certs109_153, certs109_154, certs109_155, certs109_156, certs109_157, certs109_158, certs109_159, certs109_160, certs109_161, certs109_162, certs109_163, certs109_164, certs109_165, certs109_166, certs109_167, certs109_168, certs109_169, certs109_170, certs109_171, certs109_172, certs109_173, certs109_174, certs109_175, certs109_176, certs109_177, certs109_178, certs109_179, certs109_180, certs109_181, certs109_182, certs109_183, certs109_184, certs109_185, certs109_186, certs109_187, certs109_188, certs109_189, certs109_190, certs109_191, certs109_192, certs109_193, certs109_194, certs109_195, certs109_196, certs109_197, certs109_198, certs109_199, certs109_200, certs109_201, certs109_202, certs109_203, certs109_204, certs109_205, certs109_206, certs109_207, certs109_208, certs109_209, certs109_210, certs109_211, certs109_212, certs109_213, certs109_214, certs109_215, certs109_216, certs109_217, certs109_218, certs109_219, certs109_220, certs109_221, certs109_222, certs109_223, certs109_224, certs109_225, certs109_226, certs109_227, certs109_228, certs109_229, certs109_230, certs109_231, certs109_232, certs109_233, certs109_234, certs109_235, certs109_236, certs109_237, certs109_238, certs109_239, certs109_240, certs109_241, certs109_242, certs109_243, certs109_244, certs109_245, certs109_246, certs109_247, certs109_248, certs109_249, certs109_250, certs109_251, certs109_252, certs109_253, certs109_254, certs109_255, certs109_256, certs109_257, certs109_258, certs109_259, certs109_260, certs109_261, certs109_262, certs109_263, certs109_264, certs109_265, certs109_266, certs109_267, certs109_268, certs109_269, certs109_270, certs109_271, certs109_272, certs109_273, certs109_274, certs109_275, certs109_276, certs109_277, certs109_278, certs109_279, certs109_280, certs109_281, certs109_282, certs109_283, certs109_284, certs109_285, certs109_286, certs109_287, certs109_288, certs109_289, certs109_290, certs109_291, Bool.and_self]

theorem data109_ok : mOK3 109 20 grid109 grid3_107 data109 = true := by
  unfold mOK3
  rw [data109_shapes, certs109, Bool.and_true]
  decide +kernel

/-- **No Collatz 109-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/
theorem no_109_cycle_of_floor (hR : RhinBound) {x p : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :
    numLocalMin x p ≠ 109 := fun hm =>
  mOK3_sound hR grid109_ok grid3_107_ok (by norm_num) data109_ok hx hp hcyc hx1 hx2 hm hlow

end Collatz
