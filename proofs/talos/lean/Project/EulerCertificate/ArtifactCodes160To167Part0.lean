import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code160_seq_160_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 32234, limit := 32241 } =
      .ok ((((Cache.raw.codes[160]!).body).drop 0, .end), { bytes := artifactBytes, pos := 32241, limit := 32241 }) := by
  cbv

theorem code160_decoded :
    code { bytes := artifactBytes, pos := 32230, limit := 45644 } =
      .ok (Cache.raw.codes[160]!, { bytes := artifactBytes, pos := 32241, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 32231, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 32234, limit := 32241 })
    (bodyFinish := { bytes := artifactBytes, pos := 32241, limit := 32241 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code160_seq_160_tail0_decoded
  · rfl

#print axioms code160_decoded

@[cbv_eval] theorem code161_seq_161_21_t_0_t_tail32_decoded :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 32351, limit := 32488 } =
      .ok ((((((((Cache.raw.codes[161]!).body)[21]!).childBody false)[0]!).childBody false).drop 32, .end), { bytes := artifactBytes, pos := 32480, limit := 32488 }) := by
  cbv

@[cbv_eval] theorem code161_seq_161_21_t_0_t_tail0_decoded :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 32297, limit := 32488 } =
      .ok ((((((((Cache.raw.codes[161]!).body)[21]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 32480, limit := 32488 }) := by
  cbv

@[cbv_eval] theorem code161_seq_161_21_t_tail0_decoded :
    instructionSequenceAt 219 false { bytes := artifactBytes, pos := 32295, limit := 32488 } =
      .ok ((((((Cache.raw.codes[161]!).body)[21]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 32481, limit := 32488 }) := by
  cbv

@[cbv_eval] theorem code161_seq_161_tail21_decoded :
    instructionSequenceAt 221 false { bytes := artifactBytes, pos := 32293, limit := 32488 } =
      .ok ((((Cache.raw.codes[161]!).body).drop 21, .end), { bytes := artifactBytes, pos := 32488, limit := 32488 }) := by
  cbv

@[cbv_eval] theorem code161_seq_161_tail0_decoded :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 32246, limit := 32488 } =
      .ok ((((Cache.raw.codes[161]!).body).drop 0, .end), { bytes := artifactBytes, pos := 32488, limit := 32488 }) := by
  cbv

theorem code161_decoded :
    code { bytes := artifactBytes, pos := 32241, limit := 45644 } =
      .ok (Cache.raw.codes[161]!, { bytes := artifactBytes, pos := 32488, limit := 45644 }) := by
  refine code_eq_of_parts (size := 245)
    (payload := { bytes := artifactBytes, pos := 32243, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 32246, limit := 32488 })
    (bodyFinish := { bytes := artifactBytes, pos := 32488, limit := 32488 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code161_seq_161_tail0_decoded
  · rfl

#print axioms code161_decoded

@[cbv_eval] theorem code162_seq_162_35_t_tail10_decoded :
    instructionSequenceAt 565 true { bytes := artifactBytes, pos := 32798, limit := 33105 } =
      .ok ((((((Cache.raw.codes[162]!).body)[35]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 32927, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_35_t_tail0_decoded :
    instructionSequenceAt 575 true { bytes := artifactBytes, pos := 32758, limit := 33105 } =
      .ok ((((((Cache.raw.codes[162]!).body)[35]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 32927, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_35_e_tail10_decoded :
    instructionSequenceAt 565 false { bytes := artifactBytes, pos := 32967, limit := 33105 } =
      .ok ((((((Cache.raw.codes[162]!).body)[35]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 33096, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_35_e_tail0_decoded :
    instructionSequenceAt 575 false { bytes := artifactBytes, pos := 32927, limit := 33105 } =
      .ok ((((((Cache.raw.codes[162]!).body)[35]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 33096, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_tail35_decoded :
    instructionSequenceAt 577 false { bytes := artifactBytes, pos := 32756, limit := 33105 } =
      .ok ((((Cache.raw.codes[162]!).body).drop 35, .end), { bytes := artifactBytes, pos := 33105, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_tail26_decoded :
    instructionSequenceAt 586 false { bytes := artifactBytes, pos := 32613, limit := 33105 } =
      .ok ((((Cache.raw.codes[162]!).body).drop 26, .end), { bytes := artifactBytes, pos := 33105, limit := 33105 }) := by
  cbv

@[cbv_eval] theorem code162_seq_162_tail0_decoded :
    instructionSequenceAt 612 false { bytes := artifactBytes, pos := 32493, limit := 33105 } =
      .ok ((((Cache.raw.codes[162]!).body).drop 0, .end), { bytes := artifactBytes, pos := 33105, limit := 33105 }) := by
  cbv

theorem code162_decoded :
    code { bytes := artifactBytes, pos := 32488, limit := 45644 } =
      .ok (Cache.raw.codes[162]!, { bytes := artifactBytes, pos := 33105, limit := 45644 }) := by
  refine code_eq_of_parts (size := 615)
    (payload := { bytes := artifactBytes, pos := 32490, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 32493, limit := 33105 })
    (bodyFinish := { bytes := artifactBytes, pos := 33105, limit := 33105 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code162_seq_162_tail0_decoded
  · rfl

#print axioms code162_decoded

end Project.EulerCertificate.Artifact
