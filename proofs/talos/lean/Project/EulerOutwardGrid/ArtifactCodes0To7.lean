import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 584, limit := 591 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 591, limit := 591 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 580, limit := 5728 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 591, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 581, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 584, limit := 591 })
    (bodyFinish := { bytes := artifactBytes, pos := 591, limit := 591 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 595, limit := 602 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 602, limit := 602 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 591, limit := 5728 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 602, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 592, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 595, limit := 602 })
    (bodyFinish := { bytes := artifactBytes, pos := 602, limit := 602 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 606, limit := 619 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 619, limit := 619 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 602, limit := 5728 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 619, limit := 5728 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 603, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 606, limit := 619 })
    (bodyFinish := { bytes := artifactBytes, pos := 619, limit := 619 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 623, limit := 728 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 728, limit := 728 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 619, limit := 5728 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 728, limit := 5728 }) := by
  refine code_eq_of_parts (size := 108)
    (payload := { bytes := artifactBytes, pos := 620, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 623, limit := 728 })
    (bodyFinish := { bytes := artifactBytes, pos := 728, limit := 728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 732, limit := 770 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 770, limit := 770 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 728, limit := 5728 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 770, limit := 5728 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 729, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 732, limit := 770 })
    (bodyFinish := { bytes := artifactBytes, pos := 770, limit := 770 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 774, limit := 793 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 793, limit := 793 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 770, limit := 5728 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 793, limit := 5728 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 771, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 774, limit := 793 })
    (bodyFinish := { bytes := artifactBytes, pos := 793, limit := 793 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 797, limit := 830 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 830, limit := 830 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 793, limit := 5728 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 830, limit := 5728 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 794, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 797, limit := 830 })
    (bodyFinish := { bytes := artifactBytes, pos := 830, limit := 830 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 834, limit := 958 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 958, limit := 958 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 830, limit := 5728 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 958, limit := 5728 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 831, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 834, limit := 958 })
    (bodyFinish := { bytes := artifactBytes, pos := 958, limit := 958 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerOutwardGrid.Artifact
