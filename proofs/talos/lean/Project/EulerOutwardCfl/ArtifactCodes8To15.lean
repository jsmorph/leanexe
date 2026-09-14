import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_7_e_tail4_decoded :
    instructionSequenceAt 191 false { bytes := artifactBytes, pos := 981, limit := 1056 } =
      .ok ((((((Cache.raw.codes[8]!).body)[7]!).childBody true).drop 4, .end), { bytes := artifactBytes, pos := 1053, limit := 1056 }) := by
  cbv

@[cbv_eval] theorem code8_seq_8_7_e_tail0_decoded :
    instructionSequenceAt 195 false { bytes := artifactBytes, pos := 876, limit := 1056 } =
      .ok ((((((Cache.raw.codes[8]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 1053, limit := 1056 }) := by
  cbv

@[cbv_eval] theorem code8_seq_8_tail8_decoded :
    instructionSequenceAt 196 false { bytes := artifactBytes, pos := 1053, limit := 1056 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 8, .end), { bytes := artifactBytes, pos := 1056, limit := 1056 }) := by
  cbv

@[cbv_eval] theorem code8_seq_8_tail7_decoded :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 869, limit := 1056 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 7, .end), { bytes := artifactBytes, pos := 1056, limit := 1056 }) := by
  cbv

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 852, limit := 1056 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1056, limit := 1056 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 847, limit := 2557 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1056, limit := 2557 }) := by
  refine code_eq_of_parts (size := 207)
    (payload := { bytes := artifactBytes, pos := 849, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 852, limit := 1056 })
    (bodyFinish := { bytes := artifactBytes, pos := 1056, limit := 1056 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1060, limit := 1115 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1115, limit := 1115 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1056, limit := 2557 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1115, limit := 2557 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1057, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1060, limit := 1115 })
    (bodyFinish := { bytes := artifactBytes, pos := 1115, limit := 1115 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 1119, limit := 1126 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1126, limit := 1126 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1115, limit := 2557 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1126, limit := 2557 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 1116, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1119, limit := 1126 })
    (bodyFinish := { bytes := artifactBytes, pos := 1126, limit := 1126 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 1130, limit := 1168 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1168, limit := 1168 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1126, limit := 2557 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1168, limit := 2557 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 1127, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1130, limit := 1168 })
    (bodyFinish := { bytes := artifactBytes, pos := 1168, limit := 1168 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 1172, limit := 1280 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1280, limit := 1280 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1168, limit := 2557 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1280, limit := 2557 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 1169, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1172, limit := 1280 })
    (bodyFinish := { bytes := artifactBytes, pos := 1280, limit := 1280 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 1284, limit := 1291 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1291, limit := 1291 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1280, limit := 2557 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1291, limit := 2557 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 1281, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1284, limit := 1291 })
    (bodyFinish := { bytes := artifactBytes, pos := 1291, limit := 1291 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_16_t_tail27_decoded :
    instructionSequenceAt 244 true { bytes := artifactBytes, pos := 1564, limit := 1585 } =
      .ok ((((((Cache.raw.codes[14]!).body)[16]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 1565, limit := 1585 }) := by
  cbv

@[cbv_eval] theorem code14_seq_14_16_t_tail26_decoded :
    instructionSequenceAt 245 true { bytes := artifactBytes, pos := 1429, limit := 1585 } =
      .ok ((((((Cache.raw.codes[14]!).body)[16]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 1565, limit := 1585 }) := by
  cbv

@[cbv_eval] theorem code14_seq_14_16_t_tail0_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 1369, limit := 1585 } =
      .ok ((((((Cache.raw.codes[14]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1565, limit := 1585 }) := by
  cbv

@[cbv_eval] theorem code14_seq_14_tail17_decoded :
    instructionSequenceAt 272 false { bytes := artifactBytes, pos := 1580, limit := 1585 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 17, .end), { bytes := artifactBytes, pos := 1585, limit := 1585 }) := by
  cbv

@[cbv_eval] theorem code14_seq_14_tail16_decoded :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 1367, limit := 1585 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 16, .end), { bytes := artifactBytes, pos := 1585, limit := 1585 }) := by
  cbv

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 1296, limit := 1585 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1585, limit := 1585 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1291, limit := 2557 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1585, limit := 2557 }) := by
  refine code_eq_of_parts (size := 292)
    (payload := { bytes := artifactBytes, pos := 1293, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1296, limit := 1585 })
    (bodyFinish := { bytes := artifactBytes, pos := 1585, limit := 1585 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail4_decoded :
    instructionSequenceAt 134 false { bytes := artifactBytes, pos := 1607, limit := 1728 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 4, .end), { bytes := artifactBytes, pos := 1728, limit := 1728 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 1590, limit := 1728 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1728, limit := 1728 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1585, limit := 2557 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1728, limit := 2557 }) := by
  refine code_eq_of_parts (size := 141)
    (payload := { bytes := artifactBytes, pos := 1587, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1590, limit := 1728 })
    (bodyFinish := { bytes := artifactBytes, pos := 1728, limit := 1728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerOutwardCfl.Artifact
