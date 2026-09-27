import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2254, limit := 2319 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2319, limit := 2319 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2250, limit := 5260 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2319, limit := 5260 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2251, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2254, limit := 2319 })
    (bodyFinish := { bytes := artifactBytes, pos := 2319, limit := 2319 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2323, limit := 2375 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2375, limit := 2375 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2319, limit := 5260 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2375, limit := 5260 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2320, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2323, limit := 2375 })
    (bodyFinish := { bytes := artifactBytes, pos := 2375, limit := 2375 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2379, limit := 2502 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2502, limit := 2502 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2375, limit := 5260 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2502, limit := 5260 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2376, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2379, limit := 2502 })
    (bodyFinish := { bytes := artifactBytes, pos := 2502, limit := 2502 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2507, limit := 2632 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2632, limit := 2632 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2502, limit := 5260 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2632, limit := 5260 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2504, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2507, limit := 2632 })
    (bodyFinish := { bytes := artifactBytes, pos := 2632, limit := 2632 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2636, limit := 2744 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2744, limit := 2744 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2632, limit := 5260 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2744, limit := 5260 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2633, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2636, limit := 2744 })
    (bodyFinish := { bytes := artifactBytes, pos := 2744, limit := 2744 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2748, limit := 2856 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2856, limit := 2856 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2744, limit := 5260 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 2856, limit := 5260 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2745, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2748, limit := 2856 })
    (bodyFinish := { bytes := artifactBytes, pos := 2856, limit := 2856 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_47_t_tail27_decoded :
    instructionSequenceAt 270 true { bytes := artifactBytes, pos := 3186, limit := 3207 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 3187, limit := 3207 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 3050, limit := 3207 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3187, limit := 3207 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 2990, limit := 3207 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3187, limit := 3207 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail48_decoded :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 3202, limit := 3207 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 48, .end), { bytes := artifactBytes, pos := 3207, limit := 3207 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 2988, limit := 3207 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3207, limit := 3207 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 2861, limit := 3207 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3207, limit := 3207 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 2856, limit := 5260 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3207, limit := 5260 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 2858, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 2861, limit := 3207 })
    (bodyFinish := { bytes := artifactBytes, pos := 3207, limit := 3207 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3211, limit := 3319 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3319, limit := 3319 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3207, limit := 5260 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3319, limit := 5260 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3208, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3211, limit := 3319 })
    (bodyFinish := { bytes := artifactBytes, pos := 3319, limit := 3319 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerOutwardMaximum.Artifact
