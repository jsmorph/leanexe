import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 9252, limit := 9323 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9323, limit := 9323 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 9248, limit := 45644 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 9323, limit := 45644 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 9249, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9252, limit := 9323 })
    (bodyFinish := { bytes := artifactBytes, pos := 9323, limit := 9323 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 9327, limit := 9439 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9439, limit := 9439 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 9323, limit := 45644 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 9439, limit := 45644 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 9324, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9327, limit := 9439 })
    (bodyFinish := { bytes := artifactBytes, pos := 9439, limit := 9439 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 9443, limit := 9507 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9507, limit := 9507 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 9439, limit := 45644 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 9507, limit := 45644 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 9440, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9443, limit := 9507 })
    (bodyFinish := { bytes := artifactBytes, pos := 9507, limit := 9507 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail1_decoded :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 9514, limit := 9643 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 1, .end), { bytes := artifactBytes, pos := 9643, limit := 9643 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 9512, limit := 9643 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9643, limit := 9643 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 9507, limit := 45644 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 9643, limit := 45644 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 9509, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9512, limit := 9643 })
    (bodyFinish := { bytes := artifactBytes, pos := 9643, limit := 9643 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_17_t_tail28_decoded :
    instructionSequenceAt 279 true { bytes := artifactBytes, pos := 9837, limit := 9974 } =
      .ok ((((((Cache.raw.codes[44]!).body)[17]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 9966, limit := 9974 }) := by
  cbv

@[cbv_eval] theorem code44_seq_44_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 9739, limit := 9974 } =
      .ok ((((((Cache.raw.codes[44]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 9966, limit := 9974 }) := by
  cbv

@[cbv_eval] theorem code44_seq_44_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 9737, limit := 9974 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 17, .end), { bytes := artifactBytes, pos := 9974, limit := 9974 }) := by
  cbv

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 9648, limit := 9974 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9974, limit := 9974 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 9643, limit := 45644 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 9974, limit := 45644 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 9645, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9648, limit := 9974 })
    (bodyFinish := { bytes := artifactBytes, pos := 9974, limit := 9974 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 9978, limit := 10057 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10057, limit := 10057 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 9974, limit := 45644 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 10057, limit := 45644 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 9975, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9978, limit := 10057 })
    (bodyFinish := { bytes := artifactBytes, pos := 10057, limit := 10057 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

end Project.EulerCertificate.Artifact
