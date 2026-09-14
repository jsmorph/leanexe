import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 691, limit := 729 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 729, limit := 729 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 687, limit := 7175 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 729, limit := 7175 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 688, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 691, limit := 729 })
    (bodyFinish := { bytes := artifactBytes, pos := 729, limit := 729 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 733, limit := 752 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 752, limit := 752 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 729, limit := 7175 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 752, limit := 7175 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 730, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 733, limit := 752 })
    (bodyFinish := { bytes := artifactBytes, pos := 752, limit := 752 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 756, limit := 789 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 789, limit := 789 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 752, limit := 7175 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 789, limit := 7175 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 753, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 756, limit := 789 })
    (bodyFinish := { bytes := artifactBytes, pos := 789, limit := 789 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 793, limit := 917 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 917, limit := 917 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 789, limit := 7175 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 917, limit := 7175 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 790, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 793, limit := 917 })
    (bodyFinish := { bytes := artifactBytes, pos := 917, limit := 917 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 921, limit := 959 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 959, limit := 959 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 917, limit := 7175 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 959, limit := 7175 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 918, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 921, limit := 959 })
    (bodyFinish := { bytes := artifactBytes, pos := 959, limit := 959 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 963, limit := 982 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 982, limit := 982 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 959, limit := 7175 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 982, limit := 7175 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 960, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 963, limit := 982 })
    (bodyFinish := { bytes := artifactBytes, pos := 982, limit := 982 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 986, limit := 1019 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1019, limit := 1019 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 982, limit := 7175 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 1019, limit := 7175 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 983, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 986, limit := 1019 })
    (bodyFinish := { bytes := artifactBytes, pos := 1019, limit := 1019 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1023, limit := 1041 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1041, limit := 1041 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 1019, limit := 7175 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 1041, limit := 7175 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1020, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 1023, limit := 1041 })
    (bodyFinish := { bytes := artifactBytes, pos := 1041, limit := 1041 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerOutwardFlux.Artifact
