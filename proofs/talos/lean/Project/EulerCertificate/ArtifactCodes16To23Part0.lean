import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_7_e_tail3_decoded :
    instructionSequenceAt 150 false { bytes := artifactBytes, pos := 7470, limit := 7605 } =
      .ok ((((((Cache.raw.codes[16]!).body)[7]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 7600, limit := 7605 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_7_e_tail0_decoded :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 7465, limit := 7605 } =
      .ok ((((((Cache.raw.codes[16]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 7600, limit := 7605 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail7_decoded :
    instructionSequenceAt 155 false { bytes := artifactBytes, pos := 7460, limit := 7605 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 7, .end), { bytes := artifactBytes, pos := 7605, limit := 7605 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 162 false { bytes := artifactBytes, pos := 7443, limit := 7605 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7605, limit := 7605 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 7438, limit := 45644 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 7605, limit := 45644 }) := by
  refine code_eq_of_parts (size := 165)
    (payload := { bytes := artifactBytes, pos := 7440, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 7443, limit := 7605 })
    (bodyFinish := { bytes := artifactBytes, pos := 7605, limit := 7605 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 109 false { bytes := artifactBytes, pos := 7609, limit := 7718 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7718, limit := 7718 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 7605, limit := 45644 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 7718, limit := 45644 }) := by
  refine code_eq_of_parts (size := 112)
    (payload := { bytes := artifactBytes, pos := 7606, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 7609, limit := 7718 })
    (bodyFinish := { bytes := artifactBytes, pos := 7718, limit := 7718 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 7722, limit := 7817 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7817, limit := 7817 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 7718, limit := 45644 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 7817, limit := 45644 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 7719, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 7722, limit := 7817 })
    (bodyFinish := { bytes := artifactBytes, pos := 7817, limit := 7817 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 91 false { bytes := artifactBytes, pos := 7821, limit := 7912 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7912, limit := 7912 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 7817, limit := 45644 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 7912, limit := 45644 }) := by
  refine code_eq_of_parts (size := 94)
    (payload := { bytes := artifactBytes, pos := 7818, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 7821, limit := 7912 })
    (bodyFinish := { bytes := artifactBytes, pos := 7912, limit := 7912 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 7916, limit := 7999 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7999, limit := 7999 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 7912, limit := 45644 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 7999, limit := 45644 }) := by
  refine code_eq_of_parts (size := 86)
    (payload := { bytes := artifactBytes, pos := 7913, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 7916, limit := 7999 })
    (bodyFinish := { bytes := artifactBytes, pos := 7999, limit := 7999 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 8003, limit := 8086 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8086, limit := 8086 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 7999, limit := 45644 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 8086, limit := 45644 }) := by
  refine code_eq_of_parts (size := 86)
    (payload := { bytes := artifactBytes, pos := 8000, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8003, limit := 8086 })
    (bodyFinish := { bytes := artifactBytes, pos := 8086, limit := 8086 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 8090, limit := 8165 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8165, limit := 8165 }) := by
  cbv

end Project.EulerCertificate.Artifact
