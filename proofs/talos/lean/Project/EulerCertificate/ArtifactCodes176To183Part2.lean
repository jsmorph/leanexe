import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes176To183Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code179_seq_179_8_t_32_t_tail12_decoded :
    instructionSequenceAt 1539 true { bytes := artifactBytes, pos := 41073, limit := 41339 } =
      .ok ((((((((Cache.raw.codes[179]!).body)[8]!).childBody false)[32]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 41202, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_32_t_tail0_decoded :
    instructionSequenceAt 1551 true { bytes := artifactBytes, pos := 41051, limit := 41339 } =
      .ok ((((((((Cache.raw.codes[179]!).body)[8]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 41202, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_4_t_tail0_decoded :
    instructionSequenceAt 1589 false { bytes := artifactBytes, pos := 39754, limit := 41339 } =
      .ok ((((((Cache.raw.codes[179]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 40815, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_tail32_decoded :
    instructionSequenceAt 1553 true { bytes := artifactBytes, pos := 41049, limit := 41339 } =
      .ok ((((((Cache.raw.codes[179]!).body)[8]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 41305, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_tail28_decoded :
    instructionSequenceAt 1557 true { bytes := artifactBytes, pos := 40877, limit := 41339 } =
      .ok ((((((Cache.raw.codes[179]!).body)[8]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 41305, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_8_t_tail0_decoded :
    instructionSequenceAt 1585 true { bytes := artifactBytes, pos := 40822, limit := 41339 } =
      .ok ((((((Cache.raw.codes[179]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 41305, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_tail8_decoded :
    instructionSequenceAt 1587 false { bytes := artifactBytes, pos := 40820, limit := 41339 } =
      .ok ((((Cache.raw.codes[179]!).body).drop 8, .end), { bytes := artifactBytes, pos := 41339, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_tail4_decoded :
    instructionSequenceAt 1591 false { bytes := artifactBytes, pos := 39752, limit := 41339 } =
      .ok ((((Cache.raw.codes[179]!).body).drop 4, .end), { bytes := artifactBytes, pos := 41339, limit := 41339 }) := by
  cbv

@[cbv_eval] theorem code179_seq_179_tail0_decoded :
    instructionSequenceAt 1595 false { bytes := artifactBytes, pos := 39744, limit := 41339 } =
      .ok ((((Cache.raw.codes[179]!).body).drop 0, .end), { bytes := artifactBytes, pos := 41339, limit := 41339 }) := by
  cbv

theorem code179_decoded :
    code { bytes := artifactBytes, pos := 39739, limit := 45644 } =
      .ok (Cache.raw.codes[179]!, { bytes := artifactBytes, pos := 41339, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1598)
    (payload := { bytes := artifactBytes, pos := 39741, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 39744, limit := 41339 })
    (bodyFinish := { bytes := artifactBytes, pos := 41339, limit := 41339 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code179_seq_179_tail0_decoded
  · rfl

#print axioms code179_decoded

@[cbv_eval] theorem code180_seq_180_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 41343, limit := 41350 } =
      .ok ((((Cache.raw.codes[180]!).body).drop 0, .end), { bytes := artifactBytes, pos := 41350, limit := 41350 }) := by
  cbv

theorem code180_decoded :
    code { bytes := artifactBytes, pos := 41339, limit := 45644 } =
      .ok (Cache.raw.codes[180]!, { bytes := artifactBytes, pos := 41350, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 41340, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 41343, limit := 41350 })
    (bodyFinish := { bytes := artifactBytes, pos := 41350, limit := 41350 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code180_seq_180_tail0_decoded
  · rfl

#print axioms code180_decoded

@[cbv_eval] theorem code181_seq_181_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 41354, limit := 41427 } =
      .ok ((((Cache.raw.codes[181]!).body).drop 0, .end), { bytes := artifactBytes, pos := 41427, limit := 41427 }) := by
  cbv

theorem code181_decoded :
    code { bytes := artifactBytes, pos := 41350, limit := 45644 } =
      .ok (Cache.raw.codes[181]!, { bytes := artifactBytes, pos := 41427, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 41351, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 41354, limit := 41427 })
    (bodyFinish := { bytes := artifactBytes, pos := 41427, limit := 41427 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code181_seq_181_tail0_decoded
  · rfl

#print axioms code181_decoded

@[cbv_eval] theorem code182_seq_182_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 41431, limit := 41438 } =
      .ok ((((Cache.raw.codes[182]!).body).drop 0, .end), { bytes := artifactBytes, pos := 41438, limit := 41438 }) := by
  cbv

theorem code182_decoded :
    code { bytes := artifactBytes, pos := 41427, limit := 45644 } =
      .ok (Cache.raw.codes[182]!, { bytes := artifactBytes, pos := 41438, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 41428, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 41431, limit := 41438 })
    (bodyFinish := { bytes := artifactBytes, pos := 41438, limit := 41438 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code182_seq_182_tail0_decoded
  · rfl

#print axioms code182_decoded

end Project.EulerCertificate.Artifact
