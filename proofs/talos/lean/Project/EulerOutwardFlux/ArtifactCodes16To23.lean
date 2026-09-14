import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail2_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 1627, limit := 1754 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 2, .end), { bytes := artifactBytes, pos := 1754, limit := 1754 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1623, limit := 1754 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1754, limit := 1754 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1618, limit := 7175 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1754, limit := 7175 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1620, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1623, limit := 1754 })
    (bodyFinish := { bytes := artifactBytes, pos := 1754, limit := 1754 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_17_t_tail29_decoded :
    instructionSequenceAt 278 true { bytes := artifactBytes, pos := 1972, limit := 2085 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 29, .otherwise), { bytes := artifactBytes, pos := 2077, limit := 2085 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1850, limit := 2085 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2077, limit := 2085 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail18_decoded :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 2082, limit := 2085 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 18, .end), { bytes := artifactBytes, pos := 2085, limit := 2085 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1848, limit := 2085 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2085, limit := 2085 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1759, limit := 2085 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2085, limit := 2085 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1754, limit := 7175 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2085, limit := 7175 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1756, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1759, limit := 2085 })
    (bodyFinish := { bytes := artifactBytes, pos := 2085, limit := 2085 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2089, limit := 2168 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2168, limit := 2168 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2085, limit := 7175 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2168, limit := 7175 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2086, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2089, limit := 2168 })
    (bodyFinish := { bytes := artifactBytes, pos := 2168, limit := 2168 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2172, limit := 2237 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2237, limit := 2237 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2168, limit := 7175 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2237, limit := 7175 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2169, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2172, limit := 2237 })
    (bodyFinish := { bytes := artifactBytes, pos := 2237, limit := 2237 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2241, limit := 2306 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2237, limit := 7175 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2306, limit := 7175 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2238, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2241, limit := 2306 })
    (bodyFinish := { bytes := artifactBytes, pos := 2306, limit := 2306 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2310, limit := 2362 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2362, limit := 2362 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2306, limit := 7175 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2362, limit := 7175 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2307, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2310, limit := 2362 })
    (bodyFinish := { bytes := artifactBytes, pos := 2362, limit := 2362 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2366, limit := 2379 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2379, limit := 2379 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2362, limit := 7175 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2379, limit := 7175 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 2363, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2366, limit := 2379 })
    (bodyFinish := { bytes := artifactBytes, pos := 2379, limit := 2379 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2383, limit := 2506 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2506, limit := 2506 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2379, limit := 7175 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2506, limit := 7175 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2380, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2383, limit := 2506 })
    (bodyFinish := { bytes := artifactBytes, pos := 2506, limit := 2506 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerOutwardFlux.Artifact
