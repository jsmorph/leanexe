import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 905, limit := 943 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 943, limit := 943 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 901, limit := 9077 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 943, limit := 9077 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 902, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 905, limit := 943 })
    (bodyFinish := { bytes := artifactBytes, pos := 943, limit := 943 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 947, limit := 966 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 966, limit := 966 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 943, limit := 9077 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 966, limit := 9077 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 944, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 947, limit := 966 })
    (bodyFinish := { bytes := artifactBytes, pos := 966, limit := 966 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 970, limit := 1003 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1003, limit := 1003 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 966, limit := 9077 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 1003, limit := 9077 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 967, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 970, limit := 1003 })
    (bodyFinish := { bytes := artifactBytes, pos := 1003, limit := 1003 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 1007, limit := 1131 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1131, limit := 1131 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 1003, limit := 9077 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 1131, limit := 9077 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 1004, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1007, limit := 1131 })
    (bodyFinish := { bytes := artifactBytes, pos := 1131, limit := 1131 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 1135, limit := 1173 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 1131, limit := 9077 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 1173, limit := 9077 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 1132, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1135, limit := 1173 })
    (bodyFinish := { bytes := artifactBytes, pos := 1173, limit := 1173 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 1177, limit := 1196 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1196, limit := 1196 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 1173, limit := 9077 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 1196, limit := 9077 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 1174, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1177, limit := 1196 })
    (bodyFinish := { bytes := artifactBytes, pos := 1196, limit := 1196 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1200, limit := 1233 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1233, limit := 1233 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 1196, limit := 9077 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 1233, limit := 9077 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 1197, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1200, limit := 1233 })
    (bodyFinish := { bytes := artifactBytes, pos := 1233, limit := 1233 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1237, limit := 1255 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1255, limit := 1255 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 1233, limit := 9077 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 1255, limit := 9077 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1234, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 1237, limit := 1255 })
    (bodyFinish := { bytes := artifactBytes, pos := 1255, limit := 1255 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerOutwardFaceStep.Artifact
