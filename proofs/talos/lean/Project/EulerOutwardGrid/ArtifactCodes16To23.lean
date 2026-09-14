import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1345, limit := 1400 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1400, limit := 1400 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1341, limit := 5728 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1400, limit := 5728 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1342, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1345, limit := 1400 })
    (bodyFinish := { bytes := artifactBytes, pos := 1400, limit := 1400 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1404, limit := 1475 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1475, limit := 1475 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1400, limit := 5728 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 1475, limit := 5728 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1401, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1404, limit := 1475 })
    (bodyFinish := { bytes := artifactBytes, pos := 1475, limit := 1475 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1479, limit := 1591 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1591, limit := 1591 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 1475, limit := 5728 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 1591, limit := 5728 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1476, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1479, limit := 1591 })
    (bodyFinish := { bytes := artifactBytes, pos := 1591, limit := 1591 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1595, limit := 1659 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1659, limit := 1659 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 1591, limit := 5728 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 1659, limit := 5728 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1592, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1595, limit := 1659 })
    (bodyFinish := { bytes := artifactBytes, pos := 1659, limit := 1659 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail2_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 1668, limit := 1795 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 2, .end), { bytes := artifactBytes, pos := 1795, limit := 1795 }) := by
  cbv

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1664, limit := 1795 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1795, limit := 1795 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 1659, limit := 5728 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 1795, limit := 5728 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1661, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1664, limit := 1795 })
    (bodyFinish := { bytes := artifactBytes, pos := 1795, limit := 1795 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_17_t_tail29_decoded :
    instructionSequenceAt 278 true { bytes := artifactBytes, pos := 2013, limit := 2126 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 29, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1891, limit := 2126 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail18_decoded :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 2123, limit := 2126 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 18, .end), { bytes := artifactBytes, pos := 2126, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1889, limit := 2126 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2126, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1800, limit := 2126 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2126, limit := 2126 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 1795, limit := 5728 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2126, limit := 5728 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1797, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 1800, limit := 2126 })
    (bodyFinish := { bytes := artifactBytes, pos := 2126, limit := 2126 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2130, limit := 2209 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2209, limit := 2209 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2126, limit := 5728 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2209, limit := 5728 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2127, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2130, limit := 2209 })
    (bodyFinish := { bytes := artifactBytes, pos := 2209, limit := 2209 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2213, limit := 2278 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2278, limit := 2278 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2209, limit := 5728 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2278, limit := 5728 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2210, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2213, limit := 2278 })
    (bodyFinish := { bytes := artifactBytes, pos := 2278, limit := 2278 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerOutwardGrid.Artifact
