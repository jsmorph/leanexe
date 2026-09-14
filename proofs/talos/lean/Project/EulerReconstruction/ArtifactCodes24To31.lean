import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code24_seq_24_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 2211, limit := 2260 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2260, limit := 2260 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2207, limit := 5619 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2260, limit := 5619 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 2208, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2211, limit := 2260 })
    (bodyFinish := { bytes := artifactBytes, pos := 2260, limit := 2260 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_seq_24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_seq_25_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2264, limit := 2343 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2343, limit := 2343 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2260, limit := 5619 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2343, limit := 5619 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2261, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2264, limit := 2343 })
    (bodyFinish := { bytes := artifactBytes, pos := 2343, limit := 2343 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_seq_25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_seq_26_tail0_decoded :
    instructionSequenceAt 104 false { bytes := artifactBytes, pos := 2347, limit := 2451 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2451, limit := 2451 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2343, limit := 5619 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2451, limit := 5619 }) := by
  refine code_eq_of_parts (size := 107)
    (payload := { bytes := artifactBytes, pos := 2344, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2347, limit := 2451 })
    (bodyFinish := { bytes := artifactBytes, pos := 2451, limit := 2451 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_seq_26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_seq_27_tail0_decoded :
    instructionSequenceAt 89 false { bytes := artifactBytes, pos := 2455, limit := 2544 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2544, limit := 2544 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2451, limit := 5619 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2544, limit := 5619 }) := by
  refine code_eq_of_parts (size := 92)
    (payload := { bytes := artifactBytes, pos := 2452, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2455, limit := 2544 })
    (bodyFinish := { bytes := artifactBytes, pos := 2544, limit := 2544 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_seq_27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_seq_28_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2548, limit := 2573 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2573, limit := 2573 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2544, limit := 5619 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2573, limit := 5619 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2545, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2548, limit := 2573 })
    (bodyFinish := { bytes := artifactBytes, pos := 2573, limit := 2573 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_seq_28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_seq_29_tail0_decoded :
    instructionSequenceAt 41 false { bytes := artifactBytes, pos := 2577, limit := 2618 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2618, limit := 2618 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2573, limit := 5619 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 2618, limit := 5619 }) := by
  refine code_eq_of_parts (size := 44)
    (payload := { bytes := artifactBytes, pos := 2574, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2577, limit := 2618 })
    (bodyFinish := { bytes := artifactBytes, pos := 2618, limit := 2618 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_seq_29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_seq_30_tail95_decoded :
    instructionSequenceAt 267 false { bytes := artifactBytes, pos := 2856, limit := 2985 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 95, .end), { bytes := artifactBytes, pos := 2985, limit := 2985 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail52_decoded :
    instructionSequenceAt 310 false { bytes := artifactBytes, pos := 2727, limit := 2985 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 52, .end), { bytes := artifactBytes, pos := 2985, limit := 2985 }) := by
  cbv

@[cbv_eval] theorem code30_seq_30_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 2623, limit := 2985 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2985, limit := 2985 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 2618, limit := 5619 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 2985, limit := 5619 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 2620, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2623, limit := 2985 })
    (bodyFinish := { bytes := artifactBytes, pos := 2985, limit := 2985 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_seq_30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2989, limit := 2996 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2996, limit := 2996 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 2985, limit := 5619 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 2996, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2986, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 2989, limit := 2996 })
    (bodyFinish := { bytes := artifactBytes, pos := 2996, limit := 2996 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded


end Project.EulerReconstruction.Artifact
