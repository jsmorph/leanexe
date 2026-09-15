import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 2245, limit := 2369 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2369, limit := 2369 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 2241, limit := 30726 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 2369, limit := 30726 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 2242, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2245, limit := 2369 })
    (bodyFinish := { bytes := artifactBytes, pos := 2369, limit := 2369 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 2373, limit := 2411 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2411, limit := 2411 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 2369, limit := 30726 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 2411, limit := 30726 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 2370, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2373, limit := 2411 })
    (bodyFinish := { bytes := artifactBytes, pos := 2411, limit := 2411 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 2415, limit := 2434 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2434, limit := 2434 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 2411, limit := 30726 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 2434, limit := 30726 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 2412, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2415, limit := 2434 })
    (bodyFinish := { bytes := artifactBytes, pos := 2434, limit := 2434 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 2438, limit := 2471 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2471, limit := 2471 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 2434, limit := 30726 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 2471, limit := 30726 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 2435, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2438, limit := 2471 })
    (bodyFinish := { bytes := artifactBytes, pos := 2471, limit := 2471 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 2475, limit := 2493 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2493, limit := 2493 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 2471, limit := 30726 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 2493, limit := 30726 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 2472, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2475, limit := 2493 })
    (bodyFinish := { bytes := artifactBytes, pos := 2493, limit := 2493 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 2497, limit := 2539 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2539, limit := 2539 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 2493, limit := 30726 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 2539, limit := 30726 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 2494, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2497, limit := 2539 })
    (bodyFinish := { bytes := artifactBytes, pos := 2539, limit := 2539 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 2543, limit := 2638 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2638, limit := 2638 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 2539, limit := 30726 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 2638, limit := 30726 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 2540, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2543, limit := 2638 })
    (bodyFinish := { bytes := artifactBytes, pos := 2638, limit := 2638 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 2642, limit := 2720 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2720, limit := 2720 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 2638, limit := 30726 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 2720, limit := 30726 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 2639, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2642, limit := 2720 })
    (bodyFinish := { bytes := artifactBytes, pos := 2720, limit := 2720 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerReconstructed.Artifact
