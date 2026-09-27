import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 846, limit := 888 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 888, limit := 888 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 842, limit := 4936 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 888, limit := 4936 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 843, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 846, limit := 888 })
    (bodyFinish := { bytes := artifactBytes, pos := 888, limit := 888 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 892, limit := 987 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 987, limit := 987 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 888, limit := 4936 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 987, limit := 4936 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 889, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 892, limit := 987 })
    (bodyFinish := { bytes := artifactBytes, pos := 987, limit := 987 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 991, limit := 1069 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1069, limit := 1069 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 987, limit := 4936 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1069, limit := 4936 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 988, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 991, limit := 1069 })
    (bodyFinish := { bytes := artifactBytes, pos := 1069, limit := 1069 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1073, limit := 1101 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1101, limit := 1101 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1069, limit := 4936 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1101, limit := 4936 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1070, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1073, limit := 1101 })
    (bodyFinish := { bytes := artifactBytes, pos := 1101, limit := 1101 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1105, limit := 1160 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1160, limit := 1160 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1101, limit := 4936 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1160, limit := 4936 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1102, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1105, limit := 1160 })
    (bodyFinish := { bytes := artifactBytes, pos := 1160, limit := 1160 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1164, limit := 1235 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1235, limit := 1235 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1160, limit := 4936 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1235, limit := 4936 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1161, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1164, limit := 1235 })
    (bodyFinish := { bytes := artifactBytes, pos := 1235, limit := 1235 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1239, limit := 1351 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1351, limit := 1351 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1235, limit := 4936 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1351, limit := 4936 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1236, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1239, limit := 1351 })
    (bodyFinish := { bytes := artifactBytes, pos := 1351, limit := 1351 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1355, limit := 1419 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1419, limit := 1419 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1351, limit := 4936 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1419, limit := 4936 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1352, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1355, limit := 1419 })
    (bodyFinish := { bytes := artifactBytes, pos := 1419, limit := 1419 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded

end Project.EulerOutwardSpeed.Artifact
