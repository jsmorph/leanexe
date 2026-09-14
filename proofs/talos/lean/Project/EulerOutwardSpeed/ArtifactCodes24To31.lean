import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2312, limit := 2437 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2437, limit := 2437 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2307, limit := 4936 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2437, limit := 4936 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2309, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2312, limit := 2437 })
    (bodyFinish := { bytes := artifactBytes, pos := 2437, limit := 2437 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2441, limit := 2549 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2549, limit := 2549 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2437, limit := 4936 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2549, limit := 4936 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2438, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2441, limit := 2549 })
    (bodyFinish := { bytes := artifactBytes, pos := 2549, limit := 2549 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2553, limit := 2560 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2560, limit := 2560 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2549, limit := 4936 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2560, limit := 4936 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2550, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2553, limit := 2560 })
    (bodyFinish := { bytes := artifactBytes, pos := 2560, limit := 2560 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2564, limit := 2672 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2672, limit := 2672 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2560, limit := 4936 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2672, limit := 4936 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2561, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2564, limit := 2672 })
    (bodyFinish := { bytes := artifactBytes, pos := 2672, limit := 2672 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2676, limit := 2683 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2683, limit := 2683 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2672, limit := 4936 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2683, limit := 4936 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2673, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2676, limit := 2683 })
    (bodyFinish := { bytes := artifactBytes, pos := 2683, limit := 2683 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 2877, limit := 3034 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3014, limit := 3034 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 2817, limit := 3034 } =
      .ok ((((((Cache.raw.codes[29]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3014, limit := 3034 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 2815, limit := 3034 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3034, limit := 3034 }) := by
  cbv

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 2688, limit := 3034 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3034, limit := 3034 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2683, limit := 4936 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 3034, limit := 4936 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 2685, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2688, limit := 3034 })
    (bodyFinish := { bytes := artifactBytes, pos := 3034, limit := 3034 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3038, limit := 3146 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3146, limit := 3146 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 3034, limit := 4936 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3146, limit := 4936 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3035, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3038, limit := 3146 })
    (bodyFinish := { bytes := artifactBytes, pos := 3146, limit := 3146 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3150, limit := 3265 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3265, limit := 3265 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3146, limit := 4936 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3265, limit := 4936 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3147, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3150, limit := 3265 })
    (bodyFinish := { bytes := artifactBytes, pos := 3265, limit := 3265 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded

end Project.EulerOutwardSpeed.Artifact
