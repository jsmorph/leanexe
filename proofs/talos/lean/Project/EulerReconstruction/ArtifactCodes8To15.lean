import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1001, limit := 1043 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1043, limit := 1043 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 997, limit := 5619 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1043, limit := 5619 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 998, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1001, limit := 1043 })
    (bodyFinish := { bytes := artifactBytes, pos := 1043, limit := 1043 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1047, limit := 1142 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1142, limit := 1142 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1043, limit := 5619 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1142, limit := 5619 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1044, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1047, limit := 1142 })
    (bodyFinish := { bytes := artifactBytes, pos := 1142, limit := 1142 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1146, limit := 1224 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1224, limit := 1224 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1142, limit := 5619 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1224, limit := 5619 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1143, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1146, limit := 1224 })
    (bodyFinish := { bytes := artifactBytes, pos := 1224, limit := 1224 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1228, limit := 1256 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1256, limit := 1256 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1224, limit := 5619 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1256, limit := 5619 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1225, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1228, limit := 1256 })
    (bodyFinish := { bytes := artifactBytes, pos := 1256, limit := 1256 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1260, limit := 1315 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1315, limit := 1315 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1256, limit := 5619 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1315, limit := 5619 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1257, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1260, limit := 1315 })
    (bodyFinish := { bytes := artifactBytes, pos := 1315, limit := 1315 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1319, limit := 1390 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1390, limit := 1390 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1315, limit := 5619 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1390, limit := 5619 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1316, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1319, limit := 1390 })
    (bodyFinish := { bytes := artifactBytes, pos := 1390, limit := 1390 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1394, limit := 1506 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1506, limit := 1506 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1390, limit := 5619 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1506, limit := 5619 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1391, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1394, limit := 1506 })
    (bodyFinish := { bytes := artifactBytes, pos := 1506, limit := 1506 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1510, limit := 1574 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1574, limit := 1574 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1506, limit := 5619 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1574, limit := 5619 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1507, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1510, limit := 1574 })
    (bodyFinish := { bytes := artifactBytes, pos := 1574, limit := 1574 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerReconstruction.Artifact
