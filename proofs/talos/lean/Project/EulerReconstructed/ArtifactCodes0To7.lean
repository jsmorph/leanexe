import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 15 false { bytes := artifactBytes, pos := 1976, limit := 1991 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1991, limit := 1991 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 1972, limit := 30726 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 1991, limit := 30726 }) := by
  refine code_eq_of_parts (size := 18)
    (payload := { bytes := artifactBytes, pos := 1973, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 1976, limit := 1991 })
    (bodyFinish := { bytes := artifactBytes, pos := 1991, limit := 1991 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 1995, limit := 2002 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 1991, limit := 30726 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 2002, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 1992, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 1995, limit := 2002 })
    (bodyFinish := { bytes := artifactBytes, pos := 2002, limit := 2002 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2006, limit := 2013 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2013, limit := 2013 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 2002, limit := 30726 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 2013, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2003, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2006, limit := 2013 })
    (bodyFinish := { bytes := artifactBytes, pos := 2013, limit := 2013 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2017, limit := 2030 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2030, limit := 2030 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 2013, limit := 30726 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 2030, limit := 30726 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 2014, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2017, limit := 2030 })
    (bodyFinish := { bytes := artifactBytes, pos := 2030, limit := 2030 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 2034, limit := 2139 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2139, limit := 2139 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 2030, limit := 30726 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2139, limit := 30726 }) := by
  refine code_eq_of_parts (size := 108)
    (payload := { bytes := artifactBytes, pos := 2031, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2034, limit := 2139 })
    (bodyFinish := { bytes := artifactBytes, pos := 2139, limit := 2139 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 2143, limit := 2181 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2181, limit := 2181 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 2139, limit := 30726 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 2181, limit := 30726 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 2140, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2143, limit := 2181 })
    (bodyFinish := { bytes := artifactBytes, pos := 2181, limit := 2181 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 2185, limit := 2204 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2204, limit := 2204 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 2181, limit := 30726 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 2204, limit := 30726 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 2182, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2185, limit := 2204 })
    (bodyFinish := { bytes := artifactBytes, pos := 2204, limit := 2204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 2208, limit := 2241 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2241, limit := 2241 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 2204, limit := 30726 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 2241, limit := 30726 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 2205, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 2208, limit := 2241 })
    (bodyFinish := { bytes := artifactBytes, pos := 2241, limit := 2241 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerReconstructed.Artifact
