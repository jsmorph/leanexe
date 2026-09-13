import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Evaluate

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code20_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2744, limit := 2823 } =
      .ok (((Cache.raw.codes[20]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2823, limit := 2823 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2740, limit := 21767 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2823, limit := 21767 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2741, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2744, limit := 2823 })
    (bodyFinish := { bytes := artifactBytes, pos := 2823, limit := 2823 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 2827, limit := 2876 } =
      .ok (((Cache.raw.codes[21]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2876, limit := 2876 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2823, limit := 21767 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2876, limit := 21767 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 2824, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2827, limit := 2876 })
    (bodyFinish := { bytes := artifactBytes, pos := 2876, limit := 2876 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code23_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3721, limit := 3728 } =
      .ok (((Cache.raw.codes[23]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3728, limit := 3728 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 3717, limit := 21767 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3728, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3718, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3721, limit := 3728 })
    (bodyFinish := { bytes := artifactBytes, pos := 3728, limit := 3728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_tail0_decoded
  · rfl

#print axioms code23_decoded

@[cbv_eval] theorem code24_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3732, limit := 3739 } =
      .ok (((Cache.raw.codes[24]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3739, limit := 3739 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 3728, limit := 21767 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3739, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3729, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3732, limit := 3739 })
    (bodyFinish := { bytes := artifactBytes, pos := 3739, limit := 3739 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code24_tail0_decoded
  · rfl

#print axioms code24_decoded

@[cbv_eval] theorem code25_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3743, limit := 3750 } =
      .ok (((Cache.raw.codes[25]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3750, limit := 3750 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 3739, limit := 21767 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 3750, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3740, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3743, limit := 3750 })
    (bodyFinish := { bytes := artifactBytes, pos := 3750, limit := 3750 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code25_tail0_decoded
  · rfl

#print axioms code25_decoded

@[cbv_eval] theorem code26_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3754, limit := 3761 } =
      .ok (((Cache.raw.codes[26]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3761, limit := 3761 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 3750, limit := 21767 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3761, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3751, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3754, limit := 3761 })
    (bodyFinish := { bytes := artifactBytes, pos := 3761, limit := 3761 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code26_tail0_decoded
  · rfl

#print axioms code26_decoded

@[cbv_eval] theorem code27_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3765, limit := 3772 } =
      .ok (((Cache.raw.codes[27]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3772, limit := 3772 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 3761, limit := 21767 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 3772, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3762, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3765, limit := 3772 })
    (bodyFinish := { bytes := artifactBytes, pos := 3772, limit := 3772 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code27_tail0_decoded
  · rfl

#print axioms code27_decoded

@[cbv_eval] theorem code28_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3776, limit := 3783 } =
      .ok (((Cache.raw.codes[28]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3783, limit := 3783 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 3772, limit := 21767 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 3783, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3773, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3776, limit := 3783 })
    (bodyFinish := { bytes := artifactBytes, pos := 3783, limit := 3783 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code28_tail0_decoded
  · rfl

#print axioms code28_decoded

@[cbv_eval] theorem code29_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3787, limit := 3794 } =
      .ok (((Cache.raw.codes[29]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3794, limit := 3794 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 3783, limit := 21767 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 3794, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3784, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3787, limit := 3794 })
    (bodyFinish := { bytes := artifactBytes, pos := 3794, limit := 3794 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code29_tail0_decoded
  · rfl

#print axioms code29_decoded

@[cbv_eval] theorem code30_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3798, limit := 3805 } =
      .ok (((Cache.raw.codes[30]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3805, limit := 3805 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 3794, limit := 21767 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3805, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3795, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3798, limit := 3805 })
    (bodyFinish := { bytes := artifactBytes, pos := 3805, limit := 3805 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code30_tail0_decoded
  · rfl

#print axioms code30_decoded

@[cbv_eval] theorem code31_tail0_decoded :
    instructionSequenceAt 168 false { bytes := artifactBytes, pos := 3810, limit := 3978 } =
      .ok (((Cache.raw.codes[31]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 3978, limit := 3978 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3805, limit := 21767 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3978, limit := 21767 }) := by
  refine code_eq_of_parts (size := 171)
    (payload := { bytes := artifactBytes, pos := 3807, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3810, limit := 3978 })
    (bodyFinish := { bytes := artifactBytes, pos := 3978, limit := 3978 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_tail0_decoded
  · rfl

#print axioms code31_decoded

@[cbv_eval] theorem code32_tail25_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 4038, limit := 4312 } =
      .ok (((Cache.raw.codes[32]!).body.drop 25, .end),
        { bytes := artifactBytes, pos := 4312, limit := 4312 }) := by
  cbv

@[cbv_eval] theorem code32_tail0_decoded :
    instructionSequenceAt 329 false { bytes := artifactBytes, pos := 3983, limit := 4312 } =
      .ok (((Cache.raw.codes[32]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4312, limit := 4312 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3978, limit := 21767 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 4312, limit := 21767 }) := by
  refine code_eq_of_parts (size := 332)
    (payload := { bytes := artifactBytes, pos := 3980, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 3983, limit := 4312 })
    (bodyFinish := { bytes := artifactBytes, pos := 4312, limit := 4312 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_tail0_decoded :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 4317, limit := 4521 } =
      .ok (((Cache.raw.codes[33]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4521, limit := 4521 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 4312, limit := 21767 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 4521, limit := 21767 }) := by
  refine code_eq_of_parts (size := 207)
    (payload := { bytes := artifactBytes, pos := 4314, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4317, limit := 4521 })
    (bodyFinish := { bytes := artifactBytes, pos := 4521, limit := 4521 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_tail0_decoded :
    instructionSequenceAt 27 false { bytes := artifactBytes, pos := 4525, limit := 4552 } =
      .ok (((Cache.raw.codes[34]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4552, limit := 4552 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 4521, limit := 21767 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 4552, limit := 21767 }) := by
  refine code_eq_of_parts (size := 30)
    (payload := { bytes := artifactBytes, pos := 4522, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4525, limit := 4552 })
    (bodyFinish := { bytes := artifactBytes, pos := 4552, limit := 4552 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_tail0_decoded :
    instructionSequenceAt 82 false { bytes := artifactBytes, pos := 4556, limit := 4638 } =
      .ok (((Cache.raw.codes[35]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4638, limit := 4638 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 4552, limit := 21767 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 4638, limit := 21767 }) := by
  refine code_eq_of_parts (size := 85)
    (payload := { bytes := artifactBytes, pos := 4553, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4556, limit := 4638 })
    (bodyFinish := { bytes := artifactBytes, pos := 4638, limit := 4638 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_tail0_decoded :
    instructionSequenceAt 59 false { bytes := artifactBytes, pos := 4642, limit := 4701 } =
      .ok (((Cache.raw.codes[36]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4701, limit := 4701 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 4638, limit := 21767 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4701, limit := 21767 }) := by
  refine code_eq_of_parts (size := 62)
    (payload := { bytes := artifactBytes, pos := 4639, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4642, limit := 4701 })
    (bodyFinish := { bytes := artifactBytes, pos := 4701, limit := 4701 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_tail0_decoded :
    instructionSequenceAt 230 false { bytes := artifactBytes, pos := 4706, limit := 4936 } =
      .ok (((Cache.raw.codes[37]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4701, limit := 21767 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4936, limit := 21767 }) := by
  refine code_eq_of_parts (size := 233)
    (payload := { bytes := artifactBytes, pos := 4703, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4706, limit := 4936 })
    (bodyFinish := { bytes := artifactBytes, pos := 4936, limit := 4936 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4940, limit := 4947 } =
      .ok (((Cache.raw.codes[38]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 4947, limit := 4947 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4936, limit := 21767 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 4947, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4937, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4940, limit := 4947 })
    (bodyFinish := { bytes := artifactBytes, pos := 4947, limit := 4947 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_tail0_decoded :
    instructionSequenceAt 62 false { bytes := artifactBytes, pos := 4951, limit := 5013 } =
      .ok (((Cache.raw.codes[39]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5013, limit := 5013 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 4947, limit := 21767 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 5013, limit := 21767 }) := by
  refine code_eq_of_parts (size := 65)
    (payload := { bytes := artifactBytes, pos := 4948, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 4951, limit := 5013 })
    (bodyFinish := { bytes := artifactBytes, pos := 5013, limit := 5013 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_tail0_decoded
  · rfl

#print axioms code39_decoded

end Project.EulerRiemann.Artifact
