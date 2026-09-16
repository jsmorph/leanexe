import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code88_seq_88_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 20561, limit := 20634 } =
      .ok ((((Cache.raw.codes[88]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20634, limit := 20634 }) := by
  cbv

theorem code88_decoded :
    code { bytes := artifactBytes, pos := 20557, limit := 45644 } =
      .ok (Cache.raw.codes[88]!, { bytes := artifactBytes, pos := 20634, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 20558, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20561, limit := 20634 })
    (bodyFinish := { bytes := artifactBytes, pos := 20634, limit := 20634 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code88_seq_88_tail0_decoded
  · rfl

#print axioms code88_decoded

@[cbv_eval] theorem code89_seq_89_25_t_0_t_tail76_decoded :
    instructionSequenceAt 224 false { bytes := artifactBytes, pos := 20825, limit := 20968 } =
      .ok ((((((((Cache.raw.codes[89]!).body)[25]!).childBody false)[0]!).childBody false).drop 76, .end), { bytes := artifactBytes, pos := 20954, limit := 20968 }) := by
  cbv

@[cbv_eval] theorem code89_seq_89_25_t_0_t_tail0_decoded :
    instructionSequenceAt 300 false { bytes := artifactBytes, pos := 20698, limit := 20968 } =
      .ok ((((((((Cache.raw.codes[89]!).body)[25]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20954, limit := 20968 }) := by
  cbv

@[cbv_eval] theorem code89_seq_89_25_t_tail0_decoded :
    instructionSequenceAt 302 false { bytes := artifactBytes, pos := 20696, limit := 20968 } =
      .ok ((((((Cache.raw.codes[89]!).body)[25]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20955, limit := 20968 }) := by
  cbv

@[cbv_eval] theorem code89_seq_89_tail25_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 20694, limit := 20968 } =
      .ok ((((Cache.raw.codes[89]!).body).drop 25, .end), { bytes := artifactBytes, pos := 20968, limit := 20968 }) := by
  cbv

@[cbv_eval] theorem code89_seq_89_tail0_decoded :
    instructionSequenceAt 329 false { bytes := artifactBytes, pos := 20639, limit := 20968 } =
      .ok ((((Cache.raw.codes[89]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20968, limit := 20968 }) := by
  cbv

theorem code89_decoded :
    code { bytes := artifactBytes, pos := 20634, limit := 45644 } =
      .ok (Cache.raw.codes[89]!, { bytes := artifactBytes, pos := 20968, limit := 45644 }) := by
  refine code_eq_of_parts (size := 332)
    (payload := { bytes := artifactBytes, pos := 20636, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20639, limit := 20968 })
    (bodyFinish := { bytes := artifactBytes, pos := 20968, limit := 20968 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code89_seq_89_tail0_decoded
  · rfl

#print axioms code89_decoded

@[cbv_eval] theorem code90_seq_90_tail0_decoded :
    instructionSequenceAt 27 false { bytes := artifactBytes, pos := 20972, limit := 20999 } =
      .ok ((((Cache.raw.codes[90]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20999, limit := 20999 }) := by
  cbv

theorem code90_decoded :
    code { bytes := artifactBytes, pos := 20968, limit := 45644 } =
      .ok (Cache.raw.codes[90]!, { bytes := artifactBytes, pos := 20999, limit := 45644 }) := by
  refine code_eq_of_parts (size := 30)
    (payload := { bytes := artifactBytes, pos := 20969, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20972, limit := 20999 })
    (bodyFinish := { bytes := artifactBytes, pos := 20999, limit := 20999 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code90_seq_90_tail0_decoded
  · rfl

#print axioms code90_decoded

@[cbv_eval] theorem code91_seq_91_tail0_decoded :
    instructionSequenceAt 82 false { bytes := artifactBytes, pos := 21003, limit := 21085 } =
      .ok ((((Cache.raw.codes[91]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21085, limit := 21085 }) := by
  cbv

theorem code91_decoded :
    code { bytes := artifactBytes, pos := 20999, limit := 45644 } =
      .ok (Cache.raw.codes[91]!, { bytes := artifactBytes, pos := 21085, limit := 45644 }) := by
  refine code_eq_of_parts (size := 85)
    (payload := { bytes := artifactBytes, pos := 21000, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21003, limit := 21085 })
    (bodyFinish := { bytes := artifactBytes, pos := 21085, limit := 21085 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code91_seq_91_tail0_decoded
  · rfl

#print axioms code91_decoded

@[cbv_eval] theorem code92_seq_92_tail0_decoded :
    instructionSequenceAt 59 false { bytes := artifactBytes, pos := 21089, limit := 21148 } =
      .ok ((((Cache.raw.codes[92]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21148, limit := 21148 }) := by
  cbv

theorem code92_decoded :
    code { bytes := artifactBytes, pos := 21085, limit := 45644 } =
      .ok (Cache.raw.codes[92]!, { bytes := artifactBytes, pos := 21148, limit := 45644 }) := by
  refine code_eq_of_parts (size := 62)
    (payload := { bytes := artifactBytes, pos := 21086, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21089, limit := 21148 })
    (bodyFinish := { bytes := artifactBytes, pos := 21148, limit := 21148 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code92_seq_92_tail0_decoded
  · rfl

#print axioms code92_decoded

@[cbv_eval] theorem code93_seq_93_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 21152, limit := 21207 } =
      .ok ((((Cache.raw.codes[93]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21207, limit := 21207 }) := by
  cbv

theorem code93_decoded :
    code { bytes := artifactBytes, pos := 21148, limit := 45644 } =
      .ok (Cache.raw.codes[93]!, { bytes := artifactBytes, pos := 21207, limit := 45644 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 21149, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21152, limit := 21207 })
    (bodyFinish := { bytes := artifactBytes, pos := 21207, limit := 21207 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code93_seq_93_tail0_decoded
  · rfl

#print axioms code93_decoded

end Project.EulerCertificate.Artifact
