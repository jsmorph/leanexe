import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1045, limit := 1087 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1087, limit := 1087 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 1041, limit := 7175 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1087, limit := 7175 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1042, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1045, limit := 1087 })
    (bodyFinish := { bytes := artifactBytes, pos := 1087, limit := 1087 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1091, limit := 1186 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1186, limit := 1186 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1087, limit := 7175 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1186, limit := 7175 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1088, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1091, limit := 1186 })
    (bodyFinish := { bytes := artifactBytes, pos := 1186, limit := 1186 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1190, limit := 1268 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1268, limit := 1268 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1186, limit := 7175 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1268, limit := 7175 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1187, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1190, limit := 1268 })
    (bodyFinish := { bytes := artifactBytes, pos := 1268, limit := 1268 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1272, limit := 1300 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1300, limit := 1300 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1268, limit := 7175 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1300, limit := 7175 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1269, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1272, limit := 1300 })
    (bodyFinish := { bytes := artifactBytes, pos := 1300, limit := 1300 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1304, limit := 1359 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1359, limit := 1359 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1300, limit := 7175 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1359, limit := 7175 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1301, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1304, limit := 1359 })
    (bodyFinish := { bytes := artifactBytes, pos := 1359, limit := 1359 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1363, limit := 1434 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1434, limit := 1434 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1359, limit := 7175 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1434, limit := 7175 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1360, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1363, limit := 1434 })
    (bodyFinish := { bytes := artifactBytes, pos := 1434, limit := 1434 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1438, limit := 1550 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1550, limit := 1550 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1434, limit := 7175 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1550, limit := 7175 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1435, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1438, limit := 1550 })
    (bodyFinish := { bytes := artifactBytes, pos := 1550, limit := 1550 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1554, limit := 1618 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1618, limit := 1618 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1550, limit := 7175 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1618, limit := 7175 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1551, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1554, limit := 1618 })
    (bodyFinish := { bytes := artifactBytes, pos := 1618, limit := 1618 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerOutwardFlux.Artifact
