import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code176_seq_176_40_t_40_t_tail29_decoded :
    instructionSequenceAt 429 true { bytes := artifactBytes, pos := 39336, limit := 39645 } =
      .ok ((((((((Cache.raw.codes[176]!).body)[40]!).childBody false)[40]!).childBody false).drop 29, .otherwise), { bytes := artifactBytes, pos := 39464, limit := 39645 }) := by
  cbv

@[cbv_eval] theorem code176_seq_176_40_t_40_t_tail0_decoded :
    instructionSequenceAt 458 true { bytes := artifactBytes, pos := 39277, limit := 39645 } =
      .ok ((((((((Cache.raw.codes[176]!).body)[40]!).childBody false)[40]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 39464, limit := 39645 }) := by
  cbv

@[cbv_eval] theorem code176_seq_176_40_t_tail40_decoded :
    instructionSequenceAt 460 true { bytes := artifactBytes, pos := 39275, limit := 39645 } =
      .ok ((((((Cache.raw.codes[176]!).body)[40]!).childBody false).drop 40, .otherwise), { bytes := artifactBytes, pos := 39544, limit := 39645 }) := by
  cbv

@[cbv_eval] theorem code176_seq_176_40_t_tail0_decoded :
    instructionSequenceAt 500 true { bytes := artifactBytes, pos := 39190, limit := 39645 } =
      .ok ((((((Cache.raw.codes[176]!).body)[40]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 39544, limit := 39645 }) := by
  cbv

@[cbv_eval] theorem code176_seq_176_tail40_decoded :
    instructionSequenceAt 502 false { bytes := artifactBytes, pos := 39188, limit := 39645 } =
      .ok ((((Cache.raw.codes[176]!).body).drop 40, .end), { bytes := artifactBytes, pos := 39645, limit := 39645 }) := by
  cbv

@[cbv_eval] theorem code176_seq_176_tail0_decoded :
    instructionSequenceAt 542 false { bytes := artifactBytes, pos := 39103, limit := 39645 } =
      .ok ((((Cache.raw.codes[176]!).body).drop 0, .end), { bytes := artifactBytes, pos := 39645, limit := 39645 }) := by
  cbv

theorem code176_decoded :
    code { bytes := artifactBytes, pos := 39098, limit := 45644 } =
      .ok (Cache.raw.codes[176]!, { bytes := artifactBytes, pos := 39645, limit := 45644 }) := by
  refine code_eq_of_parts (size := 545)
    (payload := { bytes := artifactBytes, pos := 39100, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 39103, limit := 39645 })
    (bodyFinish := { bytes := artifactBytes, pos := 39645, limit := 39645 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code176_seq_176_tail0_decoded
  · rfl

#print axioms code176_decoded

@[cbv_eval] theorem code177_seq_177_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 39649, limit := 39662 } =
      .ok ((((Cache.raw.codes[177]!).body).drop 0, .end), { bytes := artifactBytes, pos := 39662, limit := 39662 }) := by
  cbv

theorem code177_decoded :
    code { bytes := artifactBytes, pos := 39645, limit := 45644 } =
      .ok (Cache.raw.codes[177]!, { bytes := artifactBytes, pos := 39662, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 39646, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 39649, limit := 39662 })
    (bodyFinish := { bytes := artifactBytes, pos := 39662, limit := 39662 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code177_seq_177_tail0_decoded
  · rfl

#print axioms code177_decoded

@[cbv_eval] theorem code178_seq_178_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 39666, limit := 39739 } =
      .ok ((((Cache.raw.codes[178]!).body).drop 0, .end), { bytes := artifactBytes, pos := 39739, limit := 39739 }) := by
  cbv

theorem code178_decoded :
    code { bytes := artifactBytes, pos := 39662, limit := 45644 } =
      .ok (Cache.raw.codes[178]!, { bytes := artifactBytes, pos := 39739, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 39663, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 39666, limit := 39739 })
    (bodyFinish := { bytes := artifactBytes, pos := 39739, limit := 39739 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code178_seq_178_tail0_decoded
  · rfl

#print axioms code178_decoded

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_t_37_t_tail8_decoded :
    instructionSequenceAt 1488 true { bytes := artifactBytes, pos := 39972, limit := 41339 } =
      .ok ((((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false)[37]!).childBody false).drop 8, .otherwise), { bytes := artifactBytes, pos := 40101, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_t_37_t_tail0_decoded :
    instructionSequenceAt 1496 true { bytes := artifactBytes, pos := 39949, limit := 41339 } =
      .ok ((((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false)[37]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 40101, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_28_t_0_t_tail18_decoded :
    instructionSequenceAt 1513 false { bytes := artifactBytes, pos := 40415, limit := 41339 } =
      .ok ((((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 40544, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_e_28_t_0_t_tail0_decoded :
    instructionSequenceAt 1531 false { bytes := artifactBytes, pos := 40383, limit := 41339 } =
      .ok ((((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 40544, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_0_t_22_t_26_t_tail37_decoded :
    instructionSequenceAt 1498 true { bytes := artifactBytes, pos := 39947, limit := 41339 } =
      .ok ((((((((((((Cache.raw.codes[179]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody false)[26]!).childBody false).drop 37, .otherwise), { bytes := artifactBytes, pos := 40171, limit := 41339 }) := by
  cbv

end Project.EulerCertificate.Artifact
