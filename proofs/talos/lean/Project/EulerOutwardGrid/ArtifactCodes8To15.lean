import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 962, limit := 1000 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1000, limit := 1000 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 958, limit := 5728 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1000, limit := 5728 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 959, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 962, limit := 1000 })
    (bodyFinish := { bytes := artifactBytes, pos := 1000, limit := 1000 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 1004, limit := 1023 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1000, limit := 5728 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1023, limit := 5728 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 1001, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1004, limit := 1023 })
    (bodyFinish := { bytes := artifactBytes, pos := 1023, limit := 1023 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1027, limit := 1060 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1060, limit := 1060 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1023, limit := 5728 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1060, limit := 5728 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 1024, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1027, limit := 1060 })
    (bodyFinish := { bytes := artifactBytes, pos := 1060, limit := 1060 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1064, limit := 1082 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1082, limit := 1082 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1060, limit := 5728 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1082, limit := 5728 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1061, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1064, limit := 1082 })
    (bodyFinish := { bytes := artifactBytes, pos := 1082, limit := 1082 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1086, limit := 1128 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1128, limit := 1128 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1082, limit := 5728 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1128, limit := 5728 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1083, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1086, limit := 1128 })
    (bodyFinish := { bytes := artifactBytes, pos := 1128, limit := 1128 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1132, limit := 1227 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1227, limit := 1227 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1128, limit := 5728 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1227, limit := 5728 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1129, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1132, limit := 1227 })
    (bodyFinish := { bytes := artifactBytes, pos := 1227, limit := 1227 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1231, limit := 1309 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1309, limit := 1309 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1227, limit := 5728 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1309, limit := 5728 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1228, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1231, limit := 1309 })
    (bodyFinish := { bytes := artifactBytes, pos := 1309, limit := 1309 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1313, limit := 1341 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1341, limit := 1341 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1309, limit := 5728 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1341, limit := 5728 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1310, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1313, limit := 1341 })
    (bodyFinish := { bytes := artifactBytes, pos := 1341, limit := 1341 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerOutwardGrid.Artifact
