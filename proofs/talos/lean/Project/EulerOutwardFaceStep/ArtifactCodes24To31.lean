import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2725, limit := 2850 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2850, limit := 2850 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2720, limit := 9077 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2850, limit := 9077 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2722, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2725, limit := 2850 })
    (bodyFinish := { bytes := artifactBytes, pos := 2850, limit := 2850 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2854, limit := 2962 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2962, limit := 2962 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2850, limit := 9077 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2962, limit := 9077 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2851, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2854, limit := 2962 })
    (bodyFinish := { bytes := artifactBytes, pos := 2962, limit := 2962 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2966, limit := 2973 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2973, limit := 2973 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2962, limit := 9077 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2973, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2963, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2966, limit := 2973 })
    (bodyFinish := { bytes := artifactBytes, pos := 2973, limit := 2973 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2977, limit := 3085 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3085, limit := 3085 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2973, limit := 9077 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 3085, limit := 9077 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2974, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 2977, limit := 3085 })
    (bodyFinish := { bytes := artifactBytes, pos := 3085, limit := 3085 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3089, limit := 3096 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3096, limit := 3096 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 3085, limit := 9077 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 3096, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3086, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3089, limit := 3096 })
    (bodyFinish := { bytes := artifactBytes, pos := 3096, limit := 3096 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_47_t_tail27_decoded :
    instructionSequenceAt 270 true { bytes := artifactBytes, pos := 3426, limit := 3447 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 3427, limit := 3447 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 3290, limit := 3447 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3427, limit := 3447 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 3230, limit := 3447 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3427, limit := 3447 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail48_decoded :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 3442, limit := 3447 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 48, .end), { bytes := artifactBytes, pos := 3447, limit := 3447 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 3228, limit := 3447 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3447, limit := 3447 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 3101, limit := 3447 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3447, limit := 3447 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 3096, limit := 9077 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 3447, limit := 9077 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 3098, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3101, limit := 3447 })
    (bodyFinish := { bytes := artifactBytes, pos := 3447, limit := 3447 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3451, limit := 3559 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3559, limit := 3559 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 3447, limit := 9077 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3559, limit := 9077 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3448, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3451, limit := 3559 })
    (bodyFinish := { bytes := artifactBytes, pos := 3559, limit := 3559 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3563, limit := 3678 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3678, limit := 3678 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3559, limit := 9077 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3678, limit := 9077 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3560, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3563, limit := 3678 })
    (bodyFinish := { bytes := artifactBytes, pos := 3678, limit := 3678 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerOutwardFaceStep.Artifact
