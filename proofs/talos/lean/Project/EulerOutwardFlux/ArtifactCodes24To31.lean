import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2511, limit := 2636 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2636, limit := 2636 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2506, limit := 7175 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2636, limit := 7175 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2508, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2511, limit := 2636 })
    (bodyFinish := { bytes := artifactBytes, pos := 2636, limit := 2636 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2640, limit := 2748 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2748, limit := 2748 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2636, limit := 7175 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2748, limit := 7175 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2637, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2640, limit := 2748 })
    (bodyFinish := { bytes := artifactBytes, pos := 2748, limit := 2748 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2752, limit := 2759 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2759, limit := 2759 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2748, limit := 7175 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2759, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2749, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2752, limit := 2759 })
    (bodyFinish := { bytes := artifactBytes, pos := 2759, limit := 2759 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2763, limit := 2871 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2871, limit := 2871 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2759, limit := 7175 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2871, limit := 7175 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2760, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2763, limit := 2871 })
    (bodyFinish := { bytes := artifactBytes, pos := 2871, limit := 2871 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2875, limit := 2882 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2882, limit := 2882 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2871, limit := 7175 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2882, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2872, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2875, limit := 2882 })
    (bodyFinish := { bytes := artifactBytes, pos := 2882, limit := 2882 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_47_t_tail27_decoded :
    instructionSequenceAt 270 true { bytes := artifactBytes, pos := 3212, limit := 3233 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 3213, limit := 3233 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 3076, limit := 3233 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3213, limit := 3233 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 3016, limit := 3233 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3213, limit := 3233 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail48_decoded :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 3228, limit := 3233 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 48, .end), { bytes := artifactBytes, pos := 3233, limit := 3233 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 3014, limit := 3233 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3233, limit := 3233 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 2887, limit := 3233 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3233, limit := 3233 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2882, limit := 7175 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 3233, limit := 7175 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 2884, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 2887, limit := 3233 })
    (bodyFinish := { bytes := artifactBytes, pos := 3233, limit := 3233 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3237, limit := 3345 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3345, limit := 3345 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 3233, limit := 7175 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3345, limit := 7175 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3234, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3237, limit := 3345 })
    (bodyFinish := { bytes := artifactBytes, pos := 3345, limit := 3345 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3349, limit := 3464 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3464, limit := 3464 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3345, limit := 7175 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3464, limit := 7175 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3346, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3349, limit := 3464 })
    (bodyFinish := { bytes := artifactBytes, pos := 3464, limit := 3464 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerOutwardFlux.Artifact
