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

@[cbv_eval] theorem code40_tail142_decoded :
    instructionSequenceAt 499 false { bytes := artifactBytes, pos := 5402, limit := 5659 } =
      .ok (((Cache.raw.codes[40]!).body.drop 142, .end),
        { bytes := artifactBytes, pos := 5659, limit := 5659 }) := by
  cbv

@[cbv_eval] theorem code40_tail44_decoded :
    instructionSequenceAt 597 false { bytes := artifactBytes, pos := 5146, limit := 5659 } =
      .ok (((Cache.raw.codes[40]!).body.drop 44, .end),
        { bytes := artifactBytes, pos := 5659, limit := 5659 }) := by
  cbv

@[cbv_eval] theorem code40_tail0_decoded :
    instructionSequenceAt 641 false { bytes := artifactBytes, pos := 5018, limit := 5659 } =
      .ok (((Cache.raw.codes[40]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5659, limit := 5659 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 5013, limit := 21767 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5659, limit := 21767 }) := by
  refine code_eq_of_parts (size := 644)
    (payload := { bytes := artifactBytes, pos := 5015, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5018, limit := 5659 })
    (bodyFinish := { bytes := artifactBytes, pos := 5659, limit := 5659 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 5663, limit := 5701 } =
      .ok (((Cache.raw.codes[41]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5701, limit := 5701 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 5659, limit := 21767 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5701, limit := 21767 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 5660, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5663, limit := 5701 })
    (bodyFinish := { bytes := artifactBytes, pos := 5701, limit := 5701 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 5705, limit := 5724 } =
      .ok (((Cache.raw.codes[42]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5724, limit := 5724 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5701, limit := 21767 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5724, limit := 21767 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 5702, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5705, limit := 5724 })
    (bodyFinish := { bytes := artifactBytes, pos := 5724, limit := 5724 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 5728, limit := 5761 } =
      .ok (((Cache.raw.codes[43]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5761, limit := 5761 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5724, limit := 21767 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5761, limit := 21767 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 5725, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5728, limit := 5761 })
    (bodyFinish := { bytes := artifactBytes, pos := 5761, limit := 5761 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 5765, limit := 5778 } =
      .ok (((Cache.raw.codes[44]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 5778, limit := 5778 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5761, limit := 21767 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5778, limit := 21767 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 5762, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5765, limit := 5778 })
    (bodyFinish := { bytes := artifactBytes, pos := 5778, limit := 5778 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_tail14_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 5878, limit := 6140 } =
      .ok (((Cache.raw.codes[45]!).body.drop 14, .end),
        { bytes := artifactBytes, pos := 6140, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem code45_tail0_decoded :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 5783, limit := 6140 } =
      .ok (((Cache.raw.codes[45]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6140, limit := 6140 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 5778, limit := 21767 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 6140, limit := 21767 }) := by
  refine code_eq_of_parts (size := 360)
    (payload := { bytes := artifactBytes, pos := 5780, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 5783, limit := 6140 })
    (bodyFinish := { bytes := artifactBytes, pos := 6140, limit := 6140 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 6144, limit := 6193 } =
      .ok (((Cache.raw.codes[46]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6193, limit := 6193 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 6140, limit := 21767 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 6193, limit := 21767 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 6141, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6144, limit := 6193 })
    (bodyFinish := { bytes := artifactBytes, pos := 6193, limit := 6193 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6197, limit := 6204 } =
      .ok (((Cache.raw.codes[47]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6204, limit := 6204 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 6193, limit := 21767 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 6204, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6194, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6197, limit := 6204 })
    (bodyFinish := { bytes := artifactBytes, pos := 6204, limit := 6204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_tail0_decoded
  · rfl

#print axioms code47_decoded

@[cbv_eval] theorem code48_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6208, limit := 6215 } =
      .ok (((Cache.raw.codes[48]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6215, limit := 6215 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 6204, limit := 21767 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 6215, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6205, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6208, limit := 6215 })
    (bodyFinish := { bytes := artifactBytes, pos := 6215, limit := 6215 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6219, limit := 6226 } =
      .ok (((Cache.raw.codes[49]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6226, limit := 6226 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 6215, limit := 21767 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 6226, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6216, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6219, limit := 6226 })
    (bodyFinish := { bytes := artifactBytes, pos := 6226, limit := 6226 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_tail0_decoded
  · rfl

#print axioms code49_decoded

@[cbv_eval] theorem code50_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6230, limit := 6237 } =
      .ok (((Cache.raw.codes[50]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6237, limit := 6237 }) := by
  cbv

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 6226, limit := 21767 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 6237, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6227, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6230, limit := 6237 })
    (bodyFinish := { bytes := artifactBytes, pos := 6237, limit := 6237 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code50_tail0_decoded
  · rfl

#print axioms code50_decoded

@[cbv_eval] theorem code51_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6241, limit := 6248 } =
      .ok (((Cache.raw.codes[51]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6248, limit := 6248 }) := by
  cbv

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 6237, limit := 21767 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 6248, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6238, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6241, limit := 6248 })
    (bodyFinish := { bytes := artifactBytes, pos := 6248, limit := 6248 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code51_tail0_decoded
  · rfl

#print axioms code51_decoded

@[cbv_eval] theorem code52_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6252, limit := 6259 } =
      .ok (((Cache.raw.codes[52]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6259, limit := 6259 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 6248, limit := 21767 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 6259, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6249, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6252, limit := 6259 })
    (bodyFinish := { bytes := artifactBytes, pos := 6259, limit := 6259 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code52_tail0_decoded
  · rfl

#print axioms code52_decoded

@[cbv_eval] theorem code53_tail0_decoded :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 6263, limit := 6300 } =
      .ok (((Cache.raw.codes[53]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6300, limit := 6300 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 6259, limit := 21767 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 6300, limit := 21767 }) := by
  refine code_eq_of_parts (size := 40)
    (payload := { bytes := artifactBytes, pos := 6260, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6263, limit := 6300 })
    (bodyFinish := { bytes := artifactBytes, pos := 6300, limit := 6300 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code53_tail0_decoded
  · rfl

#print axioms code53_decoded

@[cbv_eval] theorem code55_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6960, limit := 6967 } =
      .ok (((Cache.raw.codes[55]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6967, limit := 6967 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 6956, limit := 21767 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 6967, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6957, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6960, limit := 6967 })
    (bodyFinish := { bytes := artifactBytes, pos := 6967, limit := 6967 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code55_tail0_decoded
  · rfl

#print axioms code55_decoded

@[cbv_eval] theorem code56_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6971, limit := 6978 } =
      .ok (((Cache.raw.codes[56]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 6978, limit := 6978 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 6967, limit := 21767 } =
      .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 6978, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6968, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 6971, limit := 6978 })
    (bodyFinish := { bytes := artifactBytes, pos := 6978, limit := 6978 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code56_tail0_decoded
  · rfl

#print axioms code56_decoded

end Project.EulerRiemann.Artifact
