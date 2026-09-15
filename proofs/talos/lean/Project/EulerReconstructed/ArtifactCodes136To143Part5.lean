import Project.EulerReconstructed.ArtifactCodes136To143Part4
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code141_seq_141_4_t_tail0_decoded :
    instructionSequenceAt 1078 true { bytes := artifactBytes, pos := 25374, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 26041, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_tail28_decoded :
    instructionSequenceAt 1050 false { bytes := artifactBytes, pos := 26256, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 26434, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_tail24_decoded :
    instructionSequenceAt 1054 false { bytes := artifactBytes, pos := 26087, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody true).drop 24, .end), { bytes := artifactBytes, pos := 26434, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_tail0_decoded :
    instructionSequenceAt 1078 false { bytes := artifactBytes, pos := 26041, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 26434, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_tail4_decoded :
    instructionSequenceAt 1080 false { bytes := artifactBytes, pos := 25372, limit := 26439 } =
      .ok ((((Cache.raw.codes[141]!).body).drop 4, .end), { bytes := artifactBytes, pos := 26439, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_tail0_decoded :
    instructionSequenceAt 1084 false { bytes := artifactBytes, pos := 25355, limit := 26439 } =
      .ok ((((Cache.raw.codes[141]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26439, limit := 26439 }) := by
  cbv

theorem code141_decoded :
    code { bytes := artifactBytes, pos := 25350, limit := 30726 } =
      .ok (Cache.raw.codes[141]!, { bytes := artifactBytes, pos := 26439, limit := 30726 }) := by
  refine code_eq_of_parts (size := 1087)
    (payload := { bytes := artifactBytes, pos := 25352, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 25355, limit := 26439 })
    (bodyFinish := { bytes := artifactBytes, pos := 26439, limit := 26439 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code141_seq_141_tail0_decoded
  · rfl

#print axioms code141_decoded

@[cbv_eval] theorem code142_seq_142_4_e_28_t_0_t_tail18_decoded :
    instructionSequenceAt 469 false { bytes := artifactBytes, pos := 26652, limit := 26969 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[4]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 26780, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_28_t_0_t_tail0_decoded :
    instructionSequenceAt 487 false { bytes := artifactBytes, pos := 26621, limit := 26969 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[4]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26780, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_28_t_tail0_decoded :
    instructionSequenceAt 489 false { bytes := artifactBytes, pos := 26619, limit := 26969 } =
      .ok ((((((((Cache.raw.codes[142]!).body)[4]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26781, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_32_t_tail8_decoded :
    instructionSequenceAt 477 true { bytes := artifactBytes, pos := 26801, limit := 26969 } =
      .ok ((((((((Cache.raw.codes[142]!).body)[4]!).childBody true)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 26932, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_32_t_tail0_decoded :
    instructionSequenceAt 485 true { bytes := artifactBytes, pos := 26788, limit := 26969 } =
      .ok ((((((((Cache.raw.codes[142]!).body)[4]!).childBody true)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26932, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_tail32_decoded :
    instructionSequenceAt 487 false { bytes := artifactBytes, pos := 26786, limit := 26969 } =
      .ok ((((((Cache.raw.codes[142]!).body)[4]!).childBody true).drop 32, .end), { bytes := artifactBytes, pos := 26960, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_tail28_decoded :
    instructionSequenceAt 491 false { bytes := artifactBytes, pos := 26617, limit := 26969 } =
      .ok ((((((Cache.raw.codes[142]!).body)[4]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 26960, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_4_e_tail0_decoded :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 26563, limit := 26969 } =
      .ok ((((((Cache.raw.codes[142]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 26960, limit := 26969 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_tail4_decoded :
    instructionSequenceAt 521 false { bytes := artifactBytes, pos := 26461, limit := 26969 } =
      .ok ((((Cache.raw.codes[142]!).body).drop 4, .end), { bytes := artifactBytes, pos := 26969, limit := 26969 }) := by
  cbv


end Project.EulerReconstructed.Artifact
