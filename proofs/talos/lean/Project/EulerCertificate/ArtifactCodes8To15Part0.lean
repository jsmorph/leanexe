import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5965, limit := 5972 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5972, limit := 5972 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 5961, limit := 45644 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 5972, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5962, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5965, limit := 5972 })
    (bodyFinish := { bytes := artifactBytes, pos := 5972, limit := 5972 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 5976, limit := 5995 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5995, limit := 5995 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 5972, limit := 45644 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 5995, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 5973, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5976, limit := 5995 })
    (bodyFinish := { bytes := artifactBytes, pos := 5995, limit := 5995 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5999, limit := 6006 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6006, limit := 6006 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 5995, limit := 45644 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 6006, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5996, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5999, limit := 6006 })
    (bodyFinish := { bytes := artifactBytes, pos := 6006, limit := 6006 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6010, limit := 6017 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6017, limit := 6017 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 6006, limit := 45644 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 6017, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6007, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 6010, limit := 6017 })
    (bodyFinish := { bytes := artifactBytes, pos := 6017, limit := 6017 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 6021, limit := 6040 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6040, limit := 6040 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 6017, limit := 45644 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 6040, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 6018, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 6021, limit := 6040 })
    (bodyFinish := { bytes := artifactBytes, pos := 6040, limit := 6040 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 6044, limit := 6063 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6063, limit := 6063 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 6040, limit := 45644 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 6063, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 6041, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 6044, limit := 6063 })
    (bodyFinish := { bytes := artifactBytes, pos := 6063, limit := 6063 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 6067, limit := 6086 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6086, limit := 6086 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 6063, limit := 45644 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 6086, limit := 45644 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 6064, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 6067, limit := 6086 })
    (bodyFinish := { bytes := artifactBytes, pos := 6086, limit := 6086 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_70_t_0_t_tail18_decoded :
    instructionSequenceAt 1255 false { bytes := artifactBytes, pos := 6264, limit := 7438 } =
      .ok ((((((((Cache.raw.codes[15]!).body)[70]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 6392, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_70_t_0_t_tail0_decoded :
    instructionSequenceAt 1273 false { bytes := artifactBytes, pos := 6233, limit := 7438 } =
      .ok ((((((((Cache.raw.codes[15]!).body)[70]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6392, limit := 7438 }) := by
  cbv

end Project.EulerCertificate.Artifact
