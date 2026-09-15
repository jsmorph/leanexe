import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1259, limit := 1301 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1301, limit := 1301 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 1255, limit := 9077 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1301, limit := 9077 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1256, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1259, limit := 1301 })
    (bodyFinish := { bytes := artifactBytes, pos := 1301, limit := 1301 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1305, limit := 1400 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1400, limit := 1400 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1301, limit := 9077 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1400, limit := 9077 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1302, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1305, limit := 1400 })
    (bodyFinish := { bytes := artifactBytes, pos := 1400, limit := 1400 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1404, limit := 1482 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1482, limit := 1482 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1400, limit := 9077 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1482, limit := 9077 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1401, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1404, limit := 1482 })
    (bodyFinish := { bytes := artifactBytes, pos := 1482, limit := 1482 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1486, limit := 1514 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1514, limit := 1514 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1482, limit := 9077 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1514, limit := 9077 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1483, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1486, limit := 1514 })
    (bodyFinish := { bytes := artifactBytes, pos := 1514, limit := 1514 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1518, limit := 1573 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1573, limit := 1573 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1514, limit := 9077 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1573, limit := 9077 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1515, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1518, limit := 1573 })
    (bodyFinish := { bytes := artifactBytes, pos := 1573, limit := 1573 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1577, limit := 1648 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1648, limit := 1648 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1573, limit := 9077 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1648, limit := 9077 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1574, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1577, limit := 1648 })
    (bodyFinish := { bytes := artifactBytes, pos := 1648, limit := 1648 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1652, limit := 1764 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1764, limit := 1764 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1648, limit := 9077 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1764, limit := 9077 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1649, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1652, limit := 1764 })
    (bodyFinish := { bytes := artifactBytes, pos := 1764, limit := 1764 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1768, limit := 1832 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1832, limit := 1832 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1764, limit := 9077 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1832, limit := 9077 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1765, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1768, limit := 1832 })
    (bodyFinish := { bytes := artifactBytes, pos := 1832, limit := 1832 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerOutwardFaceStep.Artifact
