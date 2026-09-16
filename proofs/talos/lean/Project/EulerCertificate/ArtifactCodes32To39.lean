import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 8852, limit := 8871 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8871, limit := 8871 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 8848, limit := 45644 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 8871, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 8849, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8852, limit := 8871 })
    (bodyFinish := { bytes := artifactBytes, pos := 8871, limit := 8871 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 8875, limit := 8908 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8908, limit := 8908 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 8871, limit := 45644 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 8908, limit := 45644 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 8872, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8875, limit := 8908 })
    (bodyFinish := { bytes := artifactBytes, pos := 8908, limit := 8908 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 8912, limit := 8930 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8930, limit := 8930 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 8908, limit := 45644 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 8930, limit := 45644 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 8909, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8912, limit := 8930 })
    (bodyFinish := { bytes := artifactBytes, pos := 8930, limit := 8930 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 8934, limit := 8976 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8976, limit := 8976 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 8930, limit := 45644 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 8976, limit := 45644 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 8931, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8934, limit := 8976 })
    (bodyFinish := { bytes := artifactBytes, pos := 8976, limit := 8976 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 8980, limit := 9075 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9075, limit := 9075 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 8976, limit := 45644 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 9075, limit := 45644 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 8977, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8980, limit := 9075 })
    (bodyFinish := { bytes := artifactBytes, pos := 9075, limit := 9075 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 9079, limit := 9157 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9157, limit := 9157 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 9075, limit := 45644 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 9157, limit := 45644 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 9076, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9079, limit := 9157 })
    (bodyFinish := { bytes := artifactBytes, pos := 9157, limit := 9157 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 9161, limit := 9189 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9189, limit := 9189 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 9157, limit := 45644 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 9189, limit := 45644 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 9158, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9161, limit := 9189 })
    (bodyFinish := { bytes := artifactBytes, pos := 9189, limit := 9189 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 9193, limit := 9248 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9248, limit := 9248 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 9189, limit := 45644 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 9248, limit := 45644 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 9190, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 9193, limit := 9248 })
    (bodyFinish := { bytes := artifactBytes, pos := 9248, limit := 9248 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded

end Project.EulerCertificate.Artifact
