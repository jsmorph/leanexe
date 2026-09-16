import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes184To191Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code189_seq_189_4_t_tail344_decoded :
    instructionSequenceAt 1440 true { bytes := artifactBytes, pos := 43656, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 344, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail301_decoded :
    instructionSequenceAt 1483 true { bytes := artifactBytes, pos := 43527, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 301, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail253_decoded :
    instructionSequenceAt 1531 true { bytes := artifactBytes, pos := 43399, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 253, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail192_decoded :
    instructionSequenceAt 1592 true { bytes := artifactBytes, pos := 43270, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 192, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail128_decoded :
    instructionSequenceAt 1656 true { bytes := artifactBytes, pos := 43141, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 128, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail66_decoded :
    instructionSequenceAt 1718 true { bytes := artifactBytes, pos := 43011, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 66, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail4_decoded :
    instructionSequenceAt 1780 true { bytes := artifactBytes, pos := 42883, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 4, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_t_tail0_decoded :
    instructionSequenceAt 1784 true { bytes := artifactBytes, pos := 42875, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 44043, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_tail42_decoded :
    instructionSequenceAt 1742 false { bytes := artifactBytes, pos := 44329, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody true).drop 42, .end), { bytes := artifactBytes, pos := 44597, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_tail38_decoded :
    instructionSequenceAt 1746 false { bytes := artifactBytes, pos := 44134, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody true).drop 38, .end), { bytes := artifactBytes, pos := 44597, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_4_e_tail0_decoded :
    instructionSequenceAt 1784 false { bytes := artifactBytes, pos := 44043, limit := 44646 } =
      .ok ((((((Cache.raw.codes[189]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 44597, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_tail4_decoded :
    instructionSequenceAt 1786 false { bytes := artifactBytes, pos := 42873, limit := 44646 } =
      .ok ((((Cache.raw.codes[189]!).body).drop 4, .end), { bytes := artifactBytes, pos := 44646, limit := 44646 }) := by
  cbv

@[cbv_eval] theorem code189_seq_189_tail0_decoded :
    instructionSequenceAt 1790 false { bytes := artifactBytes, pos := 42856, limit := 44646 } =
      .ok ((((Cache.raw.codes[189]!).body).drop 0, .end), { bytes := artifactBytes, pos := 44646, limit := 44646 }) := by
  cbv

theorem code189_decoded :
    code { bytes := artifactBytes, pos := 42850, limit := 45644 } =
      .ok (Cache.raw.codes[189]!, { bytes := artifactBytes, pos := 44646, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1794)
    (payload := { bytes := artifactBytes, pos := 42852, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 42856, limit := 44646 })
    (bodyFinish := { bytes := artifactBytes, pos := 44646, limit := 44646 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code189_seq_189_tail0_decoded
  · rfl

#print axioms code189_decoded

@[cbv_eval] theorem code190_seq_190_tail16_decoded :
    instructionSequenceAt 146 false { bytes := artifactBytes, pos := 44684, limit := 44813 } =
      .ok ((((Cache.raw.codes[190]!).body).drop 16, .end), { bytes := artifactBytes, pos := 44813, limit := 44813 }) := by
  cbv

@[cbv_eval] theorem code190_seq_190_tail0_decoded :
    instructionSequenceAt 162 false { bytes := artifactBytes, pos := 44651, limit := 44813 } =
      .ok ((((Cache.raw.codes[190]!).body).drop 0, .end), { bytes := artifactBytes, pos := 44813, limit := 44813 }) := by
  cbv

end Project.EulerCertificate.Artifact
