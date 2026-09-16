import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code112_seq_112_tail118_decoded :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 25038, limit := 25166 } =
      .ok ((((Cache.raw.codes[112]!).body).drop 118, .end), { bytes := artifactBytes, pos := 25166, limit := 25166 }) := by
  cbv

@[cbv_eval] theorem code112_seq_112_tail109_decoded :
    instructionSequenceAt 365 false { bytes := artifactBytes, pos := 24908, limit := 25166 } =
      .ok ((((Cache.raw.codes[112]!).body).drop 109, .end), { bytes := artifactBytes, pos := 25166, limit := 25166 }) := by
  cbv

@[cbv_eval] theorem code112_seq_112_tail44_decoded :
    instructionSequenceAt 430 false { bytes := artifactBytes, pos := 24780, limit := 25166 } =
      .ok ((((Cache.raw.codes[112]!).body).drop 44, .end), { bytes := artifactBytes, pos := 25166, limit := 25166 }) := by
  cbv

@[cbv_eval] theorem code112_seq_112_tail0_decoded :
    instructionSequenceAt 474 false { bytes := artifactBytes, pos := 24692, limit := 25166 } =
      .ok ((((Cache.raw.codes[112]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25166, limit := 25166 }) := by
  cbv

theorem code112_decoded :
    code { bytes := artifactBytes, pos := 24687, limit := 45644 } =
      .ok (Cache.raw.codes[112]!, { bytes := artifactBytes, pos := 25166, limit := 45644 }) := by
  refine code_eq_of_parts (size := 477)
    (payload := { bytes := artifactBytes, pos := 24689, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24692, limit := 25166 })
    (bodyFinish := { bytes := artifactBytes, pos := 25166, limit := 25166 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code112_seq_112_tail0_decoded
  · rfl

#print axioms code112_decoded

@[cbv_eval] theorem code113_seq_113_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 25170, limit := 25177 } =
      .ok ((((Cache.raw.codes[113]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25177, limit := 25177 }) := by
  cbv

theorem code113_decoded :
    code { bytes := artifactBytes, pos := 25166, limit := 45644 } =
      .ok (Cache.raw.codes[113]!, { bytes := artifactBytes, pos := 25177, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 25167, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 25170, limit := 25177 })
    (bodyFinish := { bytes := artifactBytes, pos := 25177, limit := 25177 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code113_seq_113_tail0_decoded
  · rfl

#print axioms code113_decoded

@[cbv_eval] theorem code114_seq_114_2_t_0_t_75_e_tail1_decoded :
    instructionSequenceAt 385 false { bytes := artifactBytes, pos := 25403, limit := 25651 } =
      .ok ((((((((((Cache.raw.codes[114]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 1, .end), { bytes := artifactBytes, pos := 25531, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_2_t_0_t_75_e_tail0_decoded :
    instructionSequenceAt 386 false { bytes := artifactBytes, pos := 25401, limit := 25651 } =
      .ok ((((((((((Cache.raw.codes[114]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 25531, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_2_t_0_t_tail75_decoded :
    instructionSequenceAt 388 false { bytes := artifactBytes, pos := 25354, limit := 25651 } =
      .ok ((((((((Cache.raw.codes[114]!).body)[2]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := artifactBytes, pos := 25534, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_2_t_0_t_tail15_decoded :
    instructionSequenceAt 448 false { bytes := artifactBytes, pos := 25226, limit := 25651 } =
      .ok ((((((((Cache.raw.codes[114]!).body)[2]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := artifactBytes, pos := 25534, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_2_t_0_t_tail0_decoded :
    instructionSequenceAt 463 false { bytes := artifactBytes, pos := 25190, limit := 25651 } =
      .ok ((((((((Cache.raw.codes[114]!).body)[2]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25534, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_2_t_tail0_decoded :
    instructionSequenceAt 465 false { bytes := artifactBytes, pos := 25188, limit := 25651 } =
      .ok ((((((Cache.raw.codes[114]!).body)[2]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25535, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_tail2_decoded :
    instructionSequenceAt 467 false { bytes := artifactBytes, pos := 25186, limit := 25651 } =
      .ok ((((Cache.raw.codes[114]!).body).drop 2, .end), { bytes := artifactBytes, pos := 25651, limit := 25651 }) := by
  cbv

@[cbv_eval] theorem code114_seq_114_tail0_decoded :
    instructionSequenceAt 469 false { bytes := artifactBytes, pos := 25182, limit := 25651 } =
      .ok ((((Cache.raw.codes[114]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25651, limit := 25651 }) := by
  cbv

theorem code114_decoded :
    code { bytes := artifactBytes, pos := 25177, limit := 45644 } =
      .ok (Cache.raw.codes[114]!, { bytes := artifactBytes, pos := 25651, limit := 45644 }) := by
  refine code_eq_of_parts (size := 472)
    (payload := { bytes := artifactBytes, pos := 25179, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 25182, limit := 25651 })
    (bodyFinish := { bytes := artifactBytes, pos := 25651, limit := 25651 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code114_seq_114_tail0_decoded
  · rfl

#print axioms code114_decoded

end Project.EulerCertificate.Artifact
