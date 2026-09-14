import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail1_decoded :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 1581, limit := 1710 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 1, .end), { bytes := artifactBytes, pos := 1710, limit := 1710 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1579, limit := 1710 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1710, limit := 1710 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1574, limit := 5619 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1710, limit := 5619 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1576, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1579, limit := 1710 })
    (bodyFinish := { bytes := artifactBytes, pos := 1710, limit := 1710 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_17_t_tail28_decoded :
    instructionSequenceAt 279 true { bytes := artifactBytes, pos := 1904, limit := 2041 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 2033, limit := 2041 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1806, limit := 2041 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2033, limit := 2041 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1804, limit := 2041 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2041, limit := 2041 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1715, limit := 2041 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2041, limit := 2041 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1710, limit := 5619 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2041, limit := 5619 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1712, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 1715, limit := 2041 })
    (bodyFinish := { bytes := artifactBytes, pos := 2041, limit := 2041 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2045, limit := 2124 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2124, limit := 2124 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2041, limit := 5619 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2124, limit := 5619 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2042, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2045, limit := 2124 })
    (bodyFinish := { bytes := artifactBytes, pos := 2124, limit := 2124 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2128, limit := 2135 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2135, limit := 2135 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2124, limit := 5619 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2135, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2125, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2128, limit := 2135 })
    (bodyFinish := { bytes := artifactBytes, pos := 2135, limit := 2135 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2139, limit := 2146 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2146, limit := 2146 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2135, limit := 5619 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2146, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2136, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2139, limit := 2146 })
    (bodyFinish := { bytes := artifactBytes, pos := 2146, limit := 2146 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2150, limit := 2157 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2157, limit := 2157 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2146, limit := 5619 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2157, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2147, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2150, limit := 2157 })
    (bodyFinish := { bytes := artifactBytes, pos := 2157, limit := 2157 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2161, limit := 2168 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2168, limit := 2168 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2157, limit := 5619 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2168, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2158, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2161, limit := 2168 })
    (bodyFinish := { bytes := artifactBytes, pos := 2168, limit := 2168 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 35 false { bytes := artifactBytes, pos := 2172, limit := 2207 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2207, limit := 2207 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2168, limit := 5619 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2207, limit := 5619 }) := by
  refine code_eq_of_parts (size := 38)
    (payload := { bytes := artifactBytes, pos := 2169, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2172, limit := 2207 })
    (bodyFinish := { bytes := artifactBytes, pos := 2207, limit := 2207 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerReconstruction.Artifact
