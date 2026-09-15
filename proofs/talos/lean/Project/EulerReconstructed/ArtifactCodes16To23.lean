import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 2724, limit := 2752 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2752, limit := 2752 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 2720, limit := 30726 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 2752, limit := 30726 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 2721, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2724, limit := 2752 })
    (bodyFinish := { bytes := artifactBytes, pos := 2752, limit := 2752 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 2756, limit := 2811 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2811, limit := 2811 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 2752, limit := 30726 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2811, limit := 30726 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 2753, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2756, limit := 2811 })
    (bodyFinish := { bytes := artifactBytes, pos := 2811, limit := 2811 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 2815, limit := 2886 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2886, limit := 2886 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2811, limit := 30726 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2886, limit := 30726 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 2812, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2815, limit := 2886 })
    (bodyFinish := { bytes := artifactBytes, pos := 2886, limit := 2886 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 2890, limit := 3002 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3002, limit := 3002 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2886, limit := 30726 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 3002, limit := 30726 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 2887, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2890, limit := 3002 })
    (bodyFinish := { bytes := artifactBytes, pos := 3002, limit := 3002 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 3006, limit := 3070 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3070, limit := 3070 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 3002, limit := 30726 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 3070, limit := 30726 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 3003, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3006, limit := 3070 })
    (bodyFinish := { bytes := artifactBytes, pos := 3070, limit := 3070 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail1_decoded :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 3077, limit := 3206 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 1, .end), { bytes := artifactBytes, pos := 3206, limit := 3206 }) := by
  cbv

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 3075, limit := 3206 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3206, limit := 3206 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 3070, limit := 30726 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 3206, limit := 30726 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 3072, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3075, limit := 3206 })
    (bodyFinish := { bytes := artifactBytes, pos := 3206, limit := 3206 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_17_t_tail28_decoded :
    instructionSequenceAt 279 true { bytes := artifactBytes, pos := 3400, limit := 3537 } =
      .ok ((((((Cache.raw.codes[22]!).body)[17]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 3529, limit := 3537 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 3302, limit := 3537 } =
      .ok ((((((Cache.raw.codes[22]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3529, limit := 3537 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 3300, limit := 3537 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 17, .end), { bytes := artifactBytes, pos := 3537, limit := 3537 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 3211, limit := 3537 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3537, limit := 3537 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 3206, limit := 30726 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 3537, limit := 30726 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 3208, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3211, limit := 3537 })
    (bodyFinish := { bytes := artifactBytes, pos := 3537, limit := 3537 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 3541, limit := 3620 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3620, limit := 3620 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 3537, limit := 30726 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3620, limit := 30726 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 3538, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 3541, limit := 3620 })
    (bodyFinish := { bytes := artifactBytes, pos := 3620, limit := 3620 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded


end Project.EulerReconstructed.Artifact
