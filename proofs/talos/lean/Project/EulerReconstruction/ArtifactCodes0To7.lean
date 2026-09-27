import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 647, limit := 685 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 685, limit := 685 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 643, limit := 5619 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 685, limit := 5619 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 644, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 647, limit := 685 })
    (bodyFinish := { bytes := artifactBytes, pos := 685, limit := 685 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 689, limit := 708 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 708, limit := 708 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 685, limit := 5619 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 708, limit := 5619 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 686, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 689, limit := 708 })
    (bodyFinish := { bytes := artifactBytes, pos := 708, limit := 708 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 712, limit := 745 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 745, limit := 745 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 708, limit := 5619 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 745, limit := 5619 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 709, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 712, limit := 745 })
    (bodyFinish := { bytes := artifactBytes, pos := 745, limit := 745 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 749, limit := 873 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 873, limit := 873 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 745, limit := 5619 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 873, limit := 5619 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 746, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 749, limit := 873 })
    (bodyFinish := { bytes := artifactBytes, pos := 873, limit := 873 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 877, limit := 915 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 915, limit := 915 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 873, limit := 5619 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 915, limit := 5619 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 874, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 877, limit := 915 })
    (bodyFinish := { bytes := artifactBytes, pos := 915, limit := 915 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 919, limit := 938 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 938, limit := 938 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 915, limit := 5619 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 938, limit := 5619 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 916, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 919, limit := 938 })
    (bodyFinish := { bytes := artifactBytes, pos := 938, limit := 938 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 942, limit := 975 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 975, limit := 975 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 938, limit := 5619 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 975, limit := 5619 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 939, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 942, limit := 975 })
    (bodyFinish := { bytes := artifactBytes, pos := 975, limit := 975 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 979, limit := 997 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 997, limit := 997 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 975, limit := 5619 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 997, limit := 5619 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 976, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 979, limit := 997 })
    (bodyFinish := { bytes := artifactBytes, pos := 997, limit := 997 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerReconstruction.Artifact
