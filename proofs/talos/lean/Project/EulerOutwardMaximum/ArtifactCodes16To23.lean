import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1317, limit := 1372 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1372, limit := 1372 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1313, limit := 5260 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1372, limit := 5260 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1314, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1317, limit := 1372 })
    (bodyFinish := { bytes := artifactBytes, pos := 1372, limit := 1372 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1376, limit := 1447 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1447, limit := 1447 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1372, limit := 5260 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 1447, limit := 5260 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1373, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1376, limit := 1447 })
    (bodyFinish := { bytes := artifactBytes, pos := 1447, limit := 1447 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1451, limit := 1563 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1563, limit := 1563 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 1447, limit := 5260 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 1563, limit := 5260 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1448, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1451, limit := 1563 })
    (bodyFinish := { bytes := artifactBytes, pos := 1563, limit := 1563 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1567, limit := 1631 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1631, limit := 1631 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 1563, limit := 5260 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 1631, limit := 5260 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1564, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1567, limit := 1631 })
    (bodyFinish := { bytes := artifactBytes, pos := 1631, limit := 1631 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail2_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 1640, limit := 1767 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 2, .end), { bytes := artifactBytes, pos := 1767, limit := 1767 }) := by
  cbv

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1636, limit := 1767 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1767, limit := 1767 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 1631, limit := 5260 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 1767, limit := 5260 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1633, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1636, limit := 1767 })
    (bodyFinish := { bytes := artifactBytes, pos := 1767, limit := 1767 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_17_t_tail29_decoded :
    instructionSequenceAt 278 true { bytes := artifactBytes, pos := 1985, limit := 2098 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 29, .otherwise), { bytes := artifactBytes, pos := 2090, limit := 2098 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1863, limit := 2098 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2090, limit := 2098 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail18_decoded :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 2095, limit := 2098 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 18, .end), { bytes := artifactBytes, pos := 2098, limit := 2098 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1861, limit := 2098 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2098, limit := 2098 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1772, limit := 2098 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2098, limit := 2098 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 1767, limit := 5260 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2098, limit := 5260 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1769, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1772, limit := 2098 })
    (bodyFinish := { bytes := artifactBytes, pos := 2098, limit := 2098 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2102, limit := 2181 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2181, limit := 2181 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2098, limit := 5260 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2181, limit := 5260 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2099, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2102, limit := 2181 })
    (bodyFinish := { bytes := artifactBytes, pos := 2181, limit := 2181 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2185, limit := 2250 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2250, limit := 2250 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2181, limit := 5260 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2250, limit := 5260 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2182, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2185, limit := 2250 })
    (bodyFinish := { bytes := artifactBytes, pos := 2250, limit := 2250 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerOutwardMaximum.Artifact
