import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes184To191Part2

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code190_decoded :
    code { bytes := artifactBytes, pos := 44646, limit := 45644 } =
      .ok (Cache.raw.codes[190]!, { bytes := artifactBytes, pos := 44813, limit := 45644 }) := by
  refine code_eq_of_parts (size := 165)
    (payload := { bytes := artifactBytes, pos := 44648, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 44651, limit := 44813 })
    (bodyFinish := { bytes := artifactBytes, pos := 44813, limit := 44813 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code190_seq_190_tail0_decoded
  · rfl

#print axioms code190_decoded

@[cbv_eval] theorem code191_seq_191_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 44890, limit := 45180 } =
      .ok ((((((((Cache.raw.codes[191]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 45018, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 44859, limit := 45180 } =
      .ok ((((((((Cache.raw.codes[191]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 45018, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 44857, limit := 45180 } =
      .ok ((((((Cache.raw.codes[191]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 45019, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_22_t_tail8_decoded :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 45039, limit := 45180 } =
      .ok ((((((Cache.raw.codes[191]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 45170, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 45026, limit := 45180 } =
      .ok ((((((Cache.raw.codes[191]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 45170, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 45024, limit := 45180 } =
      .ok ((((Cache.raw.codes[191]!).body).drop 22, .end), { bytes := artifactBytes, pos := 45180, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 44855, limit := 45180 } =
      .ok ((((Cache.raw.codes[191]!).body).drop 18, .end), { bytes := artifactBytes, pos := 45180, limit := 45180 }) := by
  cbv

@[cbv_eval] theorem code191_seq_191_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 44818, limit := 45180 } =
      .ok ((((Cache.raw.codes[191]!).body).drop 0, .end), { bytes := artifactBytes, pos := 45180, limit := 45180 }) := by
  cbv

theorem code191_decoded :
    code { bytes := artifactBytes, pos := 44813, limit := 45644 } =
      .ok (Cache.raw.codes[191]!, { bytes := artifactBytes, pos := 45180, limit := 45644 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 44815, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 44818, limit := 45180 })
    (bodyFinish := { bytes := artifactBytes, pos := 45180, limit := 45180 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code191_seq_191_tail0_decoded
  · rfl

#print axioms code191_decoded

end Project.EulerCertificate.Artifact
