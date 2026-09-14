import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 556, limit := 563 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 563, limit := 563 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 552, limit := 5260 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 563, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 553, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 556, limit := 563 })
    (bodyFinish := { bytes := artifactBytes, pos := 563, limit := 563 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 567, limit := 574 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 574, limit := 574 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 563, limit := 5260 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 574, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 564, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 567, limit := 574 })
    (bodyFinish := { bytes := artifactBytes, pos := 574, limit := 574 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 578, limit := 591 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 591, limit := 591 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 574, limit := 5260 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 591, limit := 5260 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 575, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 578, limit := 591 })
    (bodyFinish := { bytes := artifactBytes, pos := 591, limit := 591 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 595, limit := 700 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 700, limit := 700 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 591, limit := 5260 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 700, limit := 5260 }) := by
  refine code_eq_of_parts (size := 108)
    (payload := { bytes := artifactBytes, pos := 592, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 595, limit := 700 })
    (bodyFinish := { bytes := artifactBytes, pos := 700, limit := 700 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 704, limit := 742 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 742, limit := 742 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 700, limit := 5260 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 742, limit := 5260 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 701, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 704, limit := 742 })
    (bodyFinish := { bytes := artifactBytes, pos := 742, limit := 742 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 746, limit := 765 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 765, limit := 765 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 742, limit := 5260 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 765, limit := 5260 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 743, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 746, limit := 765 })
    (bodyFinish := { bytes := artifactBytes, pos := 765, limit := 765 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 769, limit := 802 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 802, limit := 802 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 765, limit := 5260 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 802, limit := 5260 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 766, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 769, limit := 802 })
    (bodyFinish := { bytes := artifactBytes, pos := 802, limit := 802 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 806, limit := 930 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 930, limit := 930 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 802, limit := 5260 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 930, limit := 5260 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 803, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 806, limit := 930 })
    (bodyFinish := { bytes := artifactBytes, pos := 930, limit := 930 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerOutwardMaximum.Artifact
