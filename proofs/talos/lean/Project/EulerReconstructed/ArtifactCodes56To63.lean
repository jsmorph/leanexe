import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code56_seq_56_tail0_decoded :
    instructionSequenceAt 62 false { bytes := artifactBytes, pos := 7445, limit := 7507 } =
      .ok ((((Cache.raw.codes[56]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7507, limit := 7507 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 7441, limit := 30726 } =
      .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 7507, limit := 30726 }) := by
  refine code_eq_of_parts (size := 65)
    (payload := { bytes := artifactBytes, pos := 7442, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 7445, limit := 7507 })
    (bodyFinish := { bytes := artifactBytes, pos := 7507, limit := 7507 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code56_seq_56_tail0_decoded
  · rfl

#print axioms code56_decoded

@[cbv_eval] theorem code57_seq_57_71_t_tail10_decoded :
    instructionSequenceAt 1570 true { bytes := artifactBytes, pos := 7699, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[71]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 7828, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_71_t_tail0_decoded :
    instructionSequenceAt 1580 true { bytes := artifactBytes, pos := 7659, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[71]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7828, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_71_e_tail10_decoded :
    instructionSequenceAt 1570 false { bytes := artifactBytes, pos := 7868, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[71]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 7997, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_71_e_tail0_decoded :
    instructionSequenceAt 1580 false { bytes := artifactBytes, pos := 7828, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[71]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 7997, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_79_t_tail10_decoded :
    instructionSequenceAt 1562 true { bytes := artifactBytes, pos := 8056, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[79]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 8185, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_79_t_tail0_decoded :
    instructionSequenceAt 1572 true { bytes := artifactBytes, pos := 8016, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[79]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8185, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_79_e_tail10_decoded :
    instructionSequenceAt 1562 false { bytes := artifactBytes, pos := 8225, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[79]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 8354, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_79_e_tail0_decoded :
    instructionSequenceAt 1572 false { bytes := artifactBytes, pos := 8185, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[79]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 8354, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_115_t_tail10_decoded :
    instructionSequenceAt 1526 true { bytes := artifactBytes, pos := 8469, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[115]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 8598, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_115_t_tail0_decoded :
    instructionSequenceAt 1536 true { bytes := artifactBytes, pos := 8429, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[115]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8598, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_115_e_tail10_decoded :
    instructionSequenceAt 1526 false { bytes := artifactBytes, pos := 8638, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[115]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 8767, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_115_e_tail0_decoded :
    instructionSequenceAt 1536 false { bytes := artifactBytes, pos := 8598, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[115]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 8767, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_123_t_tail10_decoded :
    instructionSequenceAt 1518 true { bytes := artifactBytes, pos := 8826, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[123]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 8955, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_123_t_tail0_decoded :
    instructionSequenceAt 1528 true { bytes := artifactBytes, pos := 8786, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[123]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8955, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_123_e_tail10_decoded :
    instructionSequenceAt 1518 false { bytes := artifactBytes, pos := 8995, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[123]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 9124, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_123_e_tail0_decoded :
    instructionSequenceAt 1528 false { bytes := artifactBytes, pos := 8955, limit := 9165 } =
      .ok ((((((Cache.raw.codes[57]!).body)[123]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 9124, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail123_decoded :
    instructionSequenceAt 1530 false { bytes := artifactBytes, pos := 8784, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 123, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail115_decoded :
    instructionSequenceAt 1538 false { bytes := artifactBytes, pos := 8427, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 115, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail79_decoded :
    instructionSequenceAt 1574 false { bytes := artifactBytes, pos := 8014, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 79, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail71_decoded :
    instructionSequenceAt 1582 false { bytes := artifactBytes, pos := 7657, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 71, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail8_decoded :
    instructionSequenceAt 1645 false { bytes := artifactBytes, pos := 7528, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 8, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

@[cbv_eval] theorem code57_seq_57_tail0_decoded :
    instructionSequenceAt 1653 false { bytes := artifactBytes, pos := 7512, limit := 9165 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9165, limit := 9165 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 7507, limit := 30726 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 9165, limit := 30726 }) := by
  refine code_eq_of_parts (size := 1656)
    (payload := { bytes := artifactBytes, pos := 7509, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 7512, limit := 9165 })
    (bodyFinish := { bytes := artifactBytes, pos := 9165, limit := 9165 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code57_seq_57_tail0_decoded
  · rfl

#print axioms code57_decoded

@[cbv_eval] theorem code58_seq_58_tail0_decoded :
    instructionSequenceAt 35 false { bytes := artifactBytes, pos := 9169, limit := 9204 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9204, limit := 9204 }) := by
  cbv

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 9165, limit := 30726 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 9204, limit := 30726 }) := by
  refine code_eq_of_parts (size := 38)
    (payload := { bytes := artifactBytes, pos := 9166, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9169, limit := 9204 })
    (bodyFinish := { bytes := artifactBytes, pos := 9204, limit := 9204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code58_seq_58_tail0_decoded
  · rfl

#print axioms code58_decoded

@[cbv_eval] theorem code59_seq_59_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 9208, limit := 9257 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9257, limit := 9257 }) := by
  cbv

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 9204, limit := 30726 } =
      .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 9257, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 9205, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9208, limit := 9257 })
    (bodyFinish := { bytes := artifactBytes, pos := 9257, limit := 9257 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code59_seq_59_tail0_decoded
  · rfl

#print axioms code59_decoded

@[cbv_eval] theorem code60_seq_60_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 9261, limit := 9340 } =
      .ok ((((Cache.raw.codes[60]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9340, limit := 9340 }) := by
  cbv

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 9257, limit := 30726 } =
      .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 9340, limit := 30726 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 9258, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9261, limit := 9340 })
    (bodyFinish := { bytes := artifactBytes, pos := 9340, limit := 9340 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code60_seq_60_tail0_decoded
  · rfl

#print axioms code60_decoded

@[cbv_eval] theorem code61_seq_61_tail0_decoded :
    instructionSequenceAt 104 false { bytes := artifactBytes, pos := 9344, limit := 9448 } =
      .ok ((((Cache.raw.codes[61]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9448, limit := 9448 }) := by
  cbv

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 9340, limit := 30726 } =
      .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 9448, limit := 30726 }) := by
  refine code_eq_of_parts (size := 107)
    (payload := { bytes := artifactBytes, pos := 9341, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9344, limit := 9448 })
    (bodyFinish := { bytes := artifactBytes, pos := 9448, limit := 9448 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code61_seq_61_tail0_decoded
  · rfl

#print axioms code61_decoded

@[cbv_eval] theorem code62_seq_62_tail0_decoded :
    instructionSequenceAt 89 false { bytes := artifactBytes, pos := 9452, limit := 9541 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9541, limit := 9541 }) := by
  cbv

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 9448, limit := 30726 } =
      .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 9541, limit := 30726 }) := by
  refine code_eq_of_parts (size := 92)
    (payload := { bytes := artifactBytes, pos := 9449, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9452, limit := 9541 })
    (bodyFinish := { bytes := artifactBytes, pos := 9541, limit := 9541 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code62_seq_62_tail0_decoded
  · rfl

#print axioms code62_decoded

@[cbv_eval] theorem code63_seq_63_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 9545, limit := 9570 } =
      .ok ((((Cache.raw.codes[63]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9570, limit := 9570 }) := by
  cbv

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 9541, limit := 30726 } =
      .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 9570, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 9542, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9545, limit := 9570 })
    (bodyFinish := { bytes := artifactBytes, pos := 9570, limit := 9570 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code63_seq_63_tail0_decoded
  · rfl

#print axioms code63_decoded


end Project.EulerReconstructed.Artifact
