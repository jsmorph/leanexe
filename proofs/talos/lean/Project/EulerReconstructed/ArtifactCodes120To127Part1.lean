import Project.EulerReconstructed.ArtifactCodes120To127Part0
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code121_seq_121_tail34_decoded :
    instructionSequenceAt 803 false { bytes := artifactBytes, pos := 17237, limit := 17847 } =
      .ok ((((Cache.raw.codes[121]!).body).drop 34, .end), { bytes := artifactBytes, pos := 17847, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_tail30_decoded :
    instructionSequenceAt 807 false { bytes := artifactBytes, pos := 17068, limit := 17847 } =
      .ok ((((Cache.raw.codes[121]!).body).drop 30, .end), { bytes := artifactBytes, pos := 17847, limit := 17847 }) := by
  cbv

@[cbv_eval] theorem code121_seq_121_tail0_decoded :
    instructionSequenceAt 837 false { bytes := artifactBytes, pos := 17010, limit := 17847 } =
      .ok ((((Cache.raw.codes[121]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17847, limit := 17847 }) := by
  cbv

theorem code121_decoded :
    code { bytes := artifactBytes, pos := 17005, limit := 30726 } =
      .ok (Cache.raw.codes[121]!, { bytes := artifactBytes, pos := 17847, limit := 30726 }) := by
  refine code_eq_of_parts (size := 840)
    (payload := { bytes := artifactBytes, pos := 17007, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 17010, limit := 17847 })
    (bodyFinish := { bytes := artifactBytes, pos := 17847, limit := 17847 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code121_seq_121_tail0_decoded
  · rfl

#print axioms code121_decoded

@[cbv_eval] theorem code122_seq_122_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 17851, limit := 17858 } =
      .ok ((((Cache.raw.codes[122]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17858, limit := 17858 }) := by
  cbv

theorem code122_decoded :
    code { bytes := artifactBytes, pos := 17847, limit := 30726 } =
      .ok (Cache.raw.codes[122]!, { bytes := artifactBytes, pos := 17858, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 17848, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 17851, limit := 17858 })
    (bodyFinish := { bytes := artifactBytes, pos := 17858, limit := 17858 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code122_seq_122_tail0_decoded
  · rfl

#print axioms code122_decoded

@[cbv_eval] theorem code123_seq_123_21_t_0_t_tail32_decoded :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 17968, limit := 18105 } =
      .ok ((((((((Cache.raw.codes[123]!).body)[21]!).childBody false)[0]!).childBody false).drop 32, .end), { bytes := artifactBytes, pos := 18097, limit := 18105 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_21_t_0_t_tail0_decoded :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 17914, limit := 18105 } =
      .ok ((((((((Cache.raw.codes[123]!).body)[21]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18097, limit := 18105 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_21_t_tail0_decoded :
    instructionSequenceAt 219 false { bytes := artifactBytes, pos := 17912, limit := 18105 } =
      .ok ((((((Cache.raw.codes[123]!).body)[21]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18098, limit := 18105 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_tail21_decoded :
    instructionSequenceAt 221 false { bytes := artifactBytes, pos := 17910, limit := 18105 } =
      .ok ((((Cache.raw.codes[123]!).body).drop 21, .end), { bytes := artifactBytes, pos := 18105, limit := 18105 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_tail0_decoded :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 17863, limit := 18105 } =
      .ok ((((Cache.raw.codes[123]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18105, limit := 18105 }) := by
  cbv

theorem code123_decoded :
    code { bytes := artifactBytes, pos := 17858, limit := 30726 } =
      .ok (Cache.raw.codes[123]!, { bytes := artifactBytes, pos := 18105, limit := 30726 }) := by
  refine code_eq_of_parts (size := 245)
    (payload := { bytes := artifactBytes, pos := 17860, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 17863, limit := 18105 })
    (bodyFinish := { bytes := artifactBytes, pos := 18105, limit := 18105 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code123_seq_123_tail0_decoded
  · rfl

#print axioms code123_decoded

@[cbv_eval] theorem code124_seq_124_tail19_decoded :
    instructionSequenceAt 148 false { bytes := artifactBytes, pos := 18148, limit := 18277 } =
      .ok ((((Cache.raw.codes[124]!).body).drop 19, .end), { bytes := artifactBytes, pos := 18277, limit := 18277 }) := by
  cbv

@[cbv_eval] theorem code124_seq_124_tail0_decoded :
    instructionSequenceAt 167 false { bytes := artifactBytes, pos := 18110, limit := 18277 } =
      .ok ((((Cache.raw.codes[124]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18277, limit := 18277 }) := by
  cbv

theorem code124_decoded :
    code { bytes := artifactBytes, pos := 18105, limit := 30726 } =
      .ok (Cache.raw.codes[124]!, { bytes := artifactBytes, pos := 18277, limit := 30726 }) := by
  refine code_eq_of_parts (size := 170)
    (payload := { bytes := artifactBytes, pos := 18107, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 18110, limit := 18277 })
    (bodyFinish := { bytes := artifactBytes, pos := 18277, limit := 18277 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code124_seq_124_tail0_decoded
  · rfl

#print axioms code124_decoded

@[cbv_eval] theorem code125_seq_125_4_t_0_t_22_t_26_t_37_e_tail12_decoded :
    instructionSequenceAt 1252 false { bytes := artifactBytes, pos := 18543, limit := 19645 } =
      .ok ((((((((((((((Cache.raw.codes[125]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false)[37]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 18672, limit := 19645 }) := by
  cbv


end Project.EulerReconstructed.Artifact
