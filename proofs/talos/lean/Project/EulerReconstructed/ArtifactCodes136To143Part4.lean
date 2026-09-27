import Project.EulerReconstructed.ArtifactCodes136To143Part3
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code140_seq_140_tail4_decoded :
    instructionSequenceAt 2531 false { bytes := artifactBytes, pos := 22823, limit := 25350 } =
      .ok ((((Cache.raw.codes[140]!).body).drop 4, .end), { bytes := artifactBytes, pos := 25350, limit := 25350 }) := by
  cbv

@[cbv_eval] theorem code140_seq_140_tail0_decoded :
    instructionSequenceAt 2535 false { bytes := artifactBytes, pos := 22815, limit := 25350 } =
      .ok ((((Cache.raw.codes[140]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25350, limit := 25350 }) := by
  cbv

theorem code140_decoded :
    code { bytes := artifactBytes, pos := 22810, limit := 30726 } =
      .ok (Cache.raw.codes[140]!, { bytes := artifactBytes, pos := 25350, limit := 30726 }) := by
  refine code_eq_of_parts (size := 2538)
    (payload := { bytes := artifactBytes, pos := 22812, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 22815, limit := 25350 })
    (bodyFinish := { bytes := artifactBytes, pos := 25350, limit := 25350 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code140_seq_140_tail0_decoded
  · rfl

#print axioms code140_decoded

@[cbv_eval] theorem code141_seq_141_4_t_51_t_0_t_tail18_decoded :
    instructionSequenceAt 1005 false { bytes := artifactBytes, pos := 25531, limit := 26439 } =
      .ok ((((((((((Cache.raw.codes[141]!).body)[4]!).childBody false)[51]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 25659, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_51_t_0_t_tail0_decoded :
    instructionSequenceAt 1023 false { bytes := artifactBytes, pos := 25500, limit := 26439 } =
      .ok ((((((((((Cache.raw.codes[141]!).body)[4]!).childBody false)[51]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25659, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_24_t_0_t_tail18_decoded :
    instructionSequenceAt 1032 false { bytes := artifactBytes, pos := 26122, limit := 26439 } =
      .ok ((((((((((Cache.raw.codes[141]!).body)[4]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 26250, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_24_t_0_t_tail0_decoded :
    instructionSequenceAt 1050 false { bytes := artifactBytes, pos := 26091, limit := 26439 } =
      .ok ((((((((((Cache.raw.codes[141]!).body)[4]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26250, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_51_t_tail0_decoded :
    instructionSequenceAt 1025 false { bytes := artifactBytes, pos := 25498, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody false)[51]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25660, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_55_t_tail8_decoded :
    instructionSequenceAt 1013 true { bytes := artifactBytes, pos := 25680, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody false)[55]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 25811, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_55_t_tail0_decoded :
    instructionSequenceAt 1021 true { bytes := artifactBytes, pos := 25667, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody false)[55]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25811, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_24_t_tail0_decoded :
    instructionSequenceAt 1052 false { bytes := artifactBytes, pos := 26089, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody true)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26251, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_28_t_tail8_decoded :
    instructionSequenceAt 1040 true { bytes := artifactBytes, pos := 26271, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody true)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 26402, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_e_28_t_tail0_decoded :
    instructionSequenceAt 1048 true { bytes := artifactBytes, pos := 26258, limit := 26439 } =
      .ok ((((((((Cache.raw.codes[141]!).body)[4]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26402, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_tail114_decoded :
    instructionSequenceAt 964 true { bytes := artifactBytes, pos := 25913, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody false).drop 114, .otherwise), { bytes := artifactBytes, pos := 26041, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_tail55_decoded :
    instructionSequenceAt 1023 true { bytes := artifactBytes, pos := 25665, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody false).drop 55, .otherwise), { bytes := artifactBytes, pos := 26041, limit := 26439 }) := by
  cbv

@[cbv_eval] theorem code141_seq_141_4_t_tail51_decoded :
    instructionSequenceAt 1027 true { bytes := artifactBytes, pos := 25496, limit := 26439 } =
      .ok ((((((Cache.raw.codes[141]!).body)[4]!).childBody false).drop 51, .otherwise), { bytes := artifactBytes, pos := 26041, limit := 26439 }) := by
  cbv


end Project.EulerReconstructed.Artifact
