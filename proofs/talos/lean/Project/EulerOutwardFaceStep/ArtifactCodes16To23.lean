import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail2_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 1841, limit := 1968 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 2, .end), { bytes := artifactBytes, pos := 1968, limit := 1968 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1837, limit := 1968 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1968, limit := 1968 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1832, limit := 9077 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1968, limit := 9077 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1834, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1837, limit := 1968 })
    (bodyFinish := { bytes := artifactBytes, pos := 1968, limit := 1968 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_17_t_tail29_decoded :
    instructionSequenceAt 278 true { bytes := artifactBytes, pos := 2186, limit := 2299 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 29, .otherwise), { bytes := artifactBytes, pos := 2291, limit := 2299 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 2064, limit := 2299 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2291, limit := 2299 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail18_decoded :
    instructionSequenceAt 308 false { bytes := artifactBytes, pos := 2296, limit := 2299 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 18, .end), { bytes := artifactBytes, pos := 2299, limit := 2299 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 2062, limit := 2299 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2299, limit := 2299 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1973, limit := 2299 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2299, limit := 2299 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1968, limit := 9077 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2299, limit := 9077 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1970, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1973, limit := 2299 })
    (bodyFinish := { bytes := artifactBytes, pos := 2299, limit := 2299 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2303, limit := 2382 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2382, limit := 2382 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2299, limit := 9077 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2382, limit := 9077 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2300, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2303, limit := 2382 })
    (bodyFinish := { bytes := artifactBytes, pos := 2382, limit := 2382 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2386, limit := 2451 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2451, limit := 2451 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2382, limit := 9077 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2451, limit := 9077 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2383, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2386, limit := 2451 })
    (bodyFinish := { bytes := artifactBytes, pos := 2451, limit := 2451 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2455, limit := 2520 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2520, limit := 2520 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2451, limit := 9077 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2520, limit := 9077 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2452, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2455, limit := 2520 })
    (bodyFinish := { bytes := artifactBytes, pos := 2520, limit := 2520 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2524, limit := 2576 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2576, limit := 2576 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2520, limit := 9077 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2576, limit := 9077 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2521, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2524, limit := 2576 })
    (bodyFinish := { bytes := artifactBytes, pos := 2576, limit := 2576 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2580, limit := 2593 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2593, limit := 2593 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2576, limit := 9077 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2593, limit := 9077 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 2577, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2580, limit := 2593 })
    (bodyFinish := { bytes := artifactBytes, pos := 2593, limit := 2593 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2597, limit := 2720 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2720, limit := 2720 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2593, limit := 9077 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2720, limit := 9077 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2594, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2597, limit := 2720 })
    (bodyFinish := { bytes := artifactBytes, pos := 2720, limit := 2720 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerOutwardFaceStep.Artifact
