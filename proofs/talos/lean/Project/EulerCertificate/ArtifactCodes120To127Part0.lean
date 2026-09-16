import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code120_seq_120_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 26950, limit := 26969 } =
      .ok ((((Cache.raw.codes[120]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26969, limit := 26969 }) := by
  cbv

theorem code120_decoded :
    code { bytes := artifactBytes, pos := 26946, limit := 45644 } =
      .ok (Cache.raw.codes[120]!, { bytes := artifactBytes, pos := 26969, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 26947, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 26950, limit := 26969 })
    (bodyFinish := { bytes := artifactBytes, pos := 26969, limit := 26969 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code120_seq_120_tail0_decoded
  · rfl

#print axioms code120_decoded

@[cbv_eval] theorem code121_seq_121_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 26973, limit := 27006 } =
      .ok ((((Cache.raw.codes[121]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27006, limit := 27006 }) := by
  cbv

theorem code121_decoded :
    code { bytes := artifactBytes, pos := 26969, limit := 45644 } =
      .ok (Cache.raw.codes[121]!, { bytes := artifactBytes, pos := 27006, limit := 45644 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 26970, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 26973, limit := 27006 })
    (bodyFinish := { bytes := artifactBytes, pos := 27006, limit := 27006 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code121_seq_121_tail0_decoded
  · rfl

#print axioms code121_decoded

@[cbv_eval] theorem code122_seq_122_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 27010, limit := 27023 } =
      .ok ((((Cache.raw.codes[122]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27023, limit := 27023 }) := by
  cbv

theorem code122_decoded :
    code { bytes := artifactBytes, pos := 27006, limit := 45644 } =
      .ok (Cache.raw.codes[122]!, { bytes := artifactBytes, pos := 27023, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 27007, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27010, limit := 27023 })
    (bodyFinish := { bytes := artifactBytes, pos := 27023, limit := 27023 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code122_seq_122_tail0_decoded
  · rfl

#print axioms code122_decoded

@[cbv_eval] theorem code123_seq_123_18_t_tail49_decoded :
    instructionSequenceAt 288 true { bytes := artifactBytes, pos := 27225, limit := 27385 } =
      .ok ((((((Cache.raw.codes[123]!).body)[18]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 27365, limit := 27385 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_18_t_tail0_decoded :
    instructionSequenceAt 337 true { bytes := artifactBytes, pos := 27137, limit := 27385 } =
      .ok ((((((Cache.raw.codes[123]!).body)[18]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 27365, limit := 27385 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_tail18_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 27135, limit := 27385 } =
      .ok ((((Cache.raw.codes[123]!).body).drop 18, .end), { bytes := artifactBytes, pos := 27385, limit := 27385 }) := by
  cbv

@[cbv_eval] theorem code123_seq_123_tail0_decoded :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 27028, limit := 27385 } =
      .ok ((((Cache.raw.codes[123]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27385, limit := 27385 }) := by
  cbv

theorem code123_decoded :
    code { bytes := artifactBytes, pos := 27023, limit := 45644 } =
      .ok (Cache.raw.codes[123]!, { bytes := artifactBytes, pos := 27385, limit := 45644 }) := by
  refine code_eq_of_parts (size := 360)
    (payload := { bytes := artifactBytes, pos := 27025, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27028, limit := 27385 })
    (bodyFinish := { bytes := artifactBytes, pos := 27385, limit := 27385 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code123_seq_123_tail0_decoded
  · rfl

#print axioms code123_decoded

@[cbv_eval] theorem code124_seq_124_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 27389, limit := 27438 } =
      .ok ((((Cache.raw.codes[124]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27438, limit := 27438 }) := by
  cbv

theorem code124_decoded :
    code { bytes := artifactBytes, pos := 27385, limit := 45644 } =
      .ok (Cache.raw.codes[124]!, { bytes := artifactBytes, pos := 27438, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 27386, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27389, limit := 27438 })
    (bodyFinish := { bytes := artifactBytes, pos := 27438, limit := 27438 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code124_seq_124_tail0_decoded
  · rfl

#print axioms code124_decoded

@[cbv_eval] theorem code125_seq_125_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27442, limit := 27449 } =
      .ok ((((Cache.raw.codes[125]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27449, limit := 27449 }) := by
  cbv

theorem code125_decoded :
    code { bytes := artifactBytes, pos := 27438, limit := 45644 } =
      .ok (Cache.raw.codes[125]!, { bytes := artifactBytes, pos := 27449, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27439, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27442, limit := 27449 })
    (bodyFinish := { bytes := artifactBytes, pos := 27449, limit := 27449 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code125_seq_125_tail0_decoded
  · rfl

#print axioms code125_decoded

@[cbv_eval] theorem code126_seq_126_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27453, limit := 27460 } =
      .ok ((((Cache.raw.codes[126]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27460, limit := 27460 }) := by
  cbv

end Project.EulerCertificate.Artifact
