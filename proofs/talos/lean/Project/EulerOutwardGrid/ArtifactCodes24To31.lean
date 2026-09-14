import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2282, limit := 2347 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2347, limit := 2347 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2278, limit := 5728 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2347, limit := 5728 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2279, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2282, limit := 2347 })
    (bodyFinish := { bytes := artifactBytes, pos := 2347, limit := 2347 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2351, limit := 2403 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2403, limit := 2403 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2347, limit := 5728 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2403, limit := 5728 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2348, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2351, limit := 2403 })
    (bodyFinish := { bytes := artifactBytes, pos := 2403, limit := 2403 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2407, limit := 2530 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2530, limit := 2530 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2403, limit := 5728 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2530, limit := 5728 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2404, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2407, limit := 2530 })
    (bodyFinish := { bytes := artifactBytes, pos := 2530, limit := 2530 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2535, limit := 2660 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2660, limit := 2660 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2530, limit := 5728 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2660, limit := 5728 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2532, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2535, limit := 2660 })
    (bodyFinish := { bytes := artifactBytes, pos := 2660, limit := 2660 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2664, limit := 2772 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2772, limit := 2772 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2660, limit := 5728 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2772, limit := 5728 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2661, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2664, limit := 2772 })
    (bodyFinish := { bytes := artifactBytes, pos := 2772, limit := 2772 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2776, limit := 2884 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2884, limit := 2884 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2772, limit := 5728 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 2884, limit := 5728 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2773, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2776, limit := 2884 })
    (bodyFinish := { bytes := artifactBytes, pos := 2884, limit := 2884 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_47_t_tail27_decoded :
    instructionSequenceAt 270 true { bytes := artifactBytes, pos := 3214, limit := 3235 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 3215, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_47_t_tail26_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 3078, limit := 3235 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3215, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_47_t_tail0_decoded :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 3018, limit := 3235 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3215, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail48_decoded :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 3230, limit := 3235 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 48, .end), { bytes := artifactBytes, pos := 3235, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail47_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 3016, limit := 3235 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3235, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 2889, limit := 3235 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3235, limit := 3235 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 2884, limit := 5728 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3235, limit := 5728 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 2886, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 2889, limit := 3235 })
    (bodyFinish := { bytes := artifactBytes, pos := 3235, limit := 3235 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3239, limit := 3347 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3347, limit := 3347 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3235, limit := 5728 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3347, limit := 5728 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3236, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3239, limit := 3347 })
    (bodyFinish := { bytes := artifactBytes, pos := 3347, limit := 3347 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerOutwardGrid.Artifact
