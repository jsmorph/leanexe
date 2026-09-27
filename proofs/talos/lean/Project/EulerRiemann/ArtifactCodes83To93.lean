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

@[cbv_eval] theorem code83_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 11621, limit := 11628 } =
      .ok (((Cache.raw.codes[83]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 11628, limit := 11628 }) := by
  cbv

theorem code83_decoded :
    code { bytes := artifactBytes, pos := 11617, limit := 21767 } =
      .ok (Cache.raw.codes[83]!, { bytes := artifactBytes, pos := 11628, limit := 21767 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 11618, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 11621, limit := 11628 })
    (bodyFinish := { bytes := artifactBytes, pos := 11628, limit := 11628 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code83_tail0_decoded
  · rfl

#print axioms code83_decoded

@[cbv_eval] theorem code84_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 11632, limit := 11645 } =
      .ok (((Cache.raw.codes[84]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 11645, limit := 11645 }) := by
  cbv

theorem code84_decoded :
    code { bytes := artifactBytes, pos := 11628, limit := 21767 } =
      .ok (Cache.raw.codes[84]!, { bytes := artifactBytes, pos := 11645, limit := 21767 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 11629, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 11632, limit := 11645 })
    (bodyFinish := { bytes := artifactBytes, pos := 11645, limit := 11645 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code84_tail0_decoded
  · rfl

#print axioms code84_decoded

@[cbv_eval] theorem code86_tail0_decoded :
    instructionSequenceAt 162 false { bytes := artifactBytes, pos := 12155, limit := 12317 } =
      .ok (((Cache.raw.codes[86]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12317, limit := 12317 }) := by
  cbv

theorem code86_decoded :
    code { bytes := artifactBytes, pos := 12150, limit := 21767 } =
      .ok (Cache.raw.codes[86]!, { bytes := artifactBytes, pos := 12317, limit := 21767 }) := by
  refine code_eq_of_parts (size := 165)
    (payload := { bytes := artifactBytes, pos := 12152, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12155, limit := 12317 })
    (bodyFinish := { bytes := artifactBytes, pos := 12317, limit := 12317 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code86_tail0_decoded
  · rfl

#print axioms code86_decoded

@[cbv_eval] theorem code87_tail0_decoded :
    instructionSequenceAt 109 false { bytes := artifactBytes, pos := 12321, limit := 12430 } =
      .ok (((Cache.raw.codes[87]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12430, limit := 12430 }) := by
  cbv

theorem code87_decoded :
    code { bytes := artifactBytes, pos := 12317, limit := 21767 } =
      .ok (Cache.raw.codes[87]!, { bytes := artifactBytes, pos := 12430, limit := 21767 }) := by
  refine code_eq_of_parts (size := 112)
    (payload := { bytes := artifactBytes, pos := 12318, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12321, limit := 12430 })
    (bodyFinish := { bytes := artifactBytes, pos := 12430, limit := 12430 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code87_tail0_decoded
  · rfl

#print axioms code87_decoded

@[cbv_eval] theorem code88_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 12434, limit := 12529 } =
      .ok (((Cache.raw.codes[88]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12529, limit := 12529 }) := by
  cbv

theorem code88_decoded :
    code { bytes := artifactBytes, pos := 12430, limit := 21767 } =
      .ok (Cache.raw.codes[88]!, { bytes := artifactBytes, pos := 12529, limit := 21767 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 12431, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12434, limit := 12529 })
    (bodyFinish := { bytes := artifactBytes, pos := 12529, limit := 12529 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code88_tail0_decoded
  · rfl

#print axioms code88_decoded

@[cbv_eval] theorem code89_tail0_decoded :
    instructionSequenceAt 91 false { bytes := artifactBytes, pos := 12533, limit := 12624 } =
      .ok (((Cache.raw.codes[89]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12624, limit := 12624 }) := by
  cbv

theorem code89_decoded :
    code { bytes := artifactBytes, pos := 12529, limit := 21767 } =
      .ok (Cache.raw.codes[89]!, { bytes := artifactBytes, pos := 12624, limit := 21767 }) := by
  refine code_eq_of_parts (size := 94)
    (payload := { bytes := artifactBytes, pos := 12530, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12533, limit := 12624 })
    (bodyFinish := { bytes := artifactBytes, pos := 12624, limit := 12624 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code89_tail0_decoded
  · rfl

#print axioms code89_decoded

@[cbv_eval] theorem code90_tail0_decoded :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 12628, limit := 12711 } =
      .ok (((Cache.raw.codes[90]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12711, limit := 12711 }) := by
  cbv

theorem code90_decoded :
    code { bytes := artifactBytes, pos := 12624, limit := 21767 } =
      .ok (Cache.raw.codes[90]!, { bytes := artifactBytes, pos := 12711, limit := 21767 }) := by
  refine code_eq_of_parts (size := 86)
    (payload := { bytes := artifactBytes, pos := 12625, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12628, limit := 12711 })
    (bodyFinish := { bytes := artifactBytes, pos := 12711, limit := 12711 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code90_tail0_decoded
  · rfl

#print axioms code90_decoded

@[cbv_eval] theorem code91_tail0_decoded :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 12715, limit := 12798 } =
      .ok (((Cache.raw.codes[91]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12798, limit := 12798 }) := by
  cbv

theorem code91_decoded :
    code { bytes := artifactBytes, pos := 12711, limit := 21767 } =
      .ok (Cache.raw.codes[91]!, { bytes := artifactBytes, pos := 12798, limit := 21767 }) := by
  refine code_eq_of_parts (size := 86)
    (payload := { bytes := artifactBytes, pos := 12712, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12715, limit := 12798 })
    (bodyFinish := { bytes := artifactBytes, pos := 12798, limit := 12798 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code91_tail0_decoded
  · rfl

#print axioms code91_decoded

@[cbv_eval] theorem code92_tail0_decoded :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 12802, limit := 12877 } =
      .ok (((Cache.raw.codes[92]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 12877, limit := 12877 }) := by
  cbv

theorem code92_decoded :
    code { bytes := artifactBytes, pos := 12798, limit := 21767 } =
      .ok (Cache.raw.codes[92]!, { bytes := artifactBytes, pos := 12877, limit := 21767 }) := by
  refine code_eq_of_parts (size := 78)
    (payload := { bytes := artifactBytes, pos := 12799, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12802, limit := 12877 })
    (bodyFinish := { bytes := artifactBytes, pos := 12877, limit := 12877 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code92_tail0_decoded
  · rfl

#print axioms code92_decoded

@[cbv_eval] theorem code93_tail58_decoded :
    instructionSequenceAt 315 false { bytes := artifactBytes, pos := 12998, limit := 13255 } =
      .ok (((Cache.raw.codes[93]!).body.drop 58, .end),
        { bytes := artifactBytes, pos := 13255, limit := 13255 }) := by
  cbv

@[cbv_eval] theorem code93_tail0_decoded :
    instructionSequenceAt 373 false { bytes := artifactBytes, pos := 12882, limit := 13255 } =
      .ok (((Cache.raw.codes[93]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 13255, limit := 13255 }) := by
  cbv

theorem code93_decoded :
    code { bytes := artifactBytes, pos := 12877, limit := 21767 } =
      .ok (Cache.raw.codes[93]!, { bytes := artifactBytes, pos := 13255, limit := 21767 }) := by
  refine code_eq_of_parts (size := 376)
    (payload := { bytes := artifactBytes, pos := 12879, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 12882, limit := 13255 })
    (bodyFinish := { bytes := artifactBytes, pos := 13255, limit := 13255 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code93_tail0_decoded
  · rfl

#print axioms code93_decoded

end Project.EulerRiemann.Artifact
