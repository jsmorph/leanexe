import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3270, limit := 3399 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3399, limit := 3399 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3265, limit := 4936 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3399, limit := 4936 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3267, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3270, limit := 3399 })
    (bodyFinish := { bytes := artifactBytes, pos := 3399, limit := 3399 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3470, limit := 3611 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 29, .end), { bytes := artifactBytes, pos := 3611, limit := 3611 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3404, limit := 3611 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3611, limit := 3611 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3399, limit := 4936 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3611, limit := 4936 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3401, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3404, limit := 3611 })
    (bodyFinish := { bytes := artifactBytes, pos := 3611, limit := 3611 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 3615, limit := 3722 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3722, limit := 3722 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3611, limit := 4936 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3722, limit := 4936 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 3612, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3615, limit := 3722 })
    (bodyFinish := { bytes := artifactBytes, pos := 3722, limit := 3722 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3726, limit := 3841 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3841, limit := 3841 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3722, limit := 4936 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 3841, limit := 4936 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3723, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3726, limit := 3841 })
    (bodyFinish := { bytes := artifactBytes, pos := 3841, limit := 3841 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 3959, limit := 4107 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4087, limit := 4107 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 3893, limit := 4107 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4087, limit := 4107 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 3891, limit := 4107 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4107, limit := 4107 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 3846, limit := 4107 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4107, limit := 4107 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 3841, limit := 4936 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4107, limit := 4936 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 3843, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 3846, limit := 4107 })
    (bodyFinish := { bytes := artifactBytes, pos := 4107, limit := 4107 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4184, limit := 4474 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4312, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4153, limit := 4474 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4312, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4151, limit := 4474 } =
      .ok ((((((Cache.raw.codes[37]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4313, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_22_t_tail8_decoded :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 4333, limit := 4474 } =
      .ok ((((((Cache.raw.codes[37]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4464, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 4320, limit := 4474 } =
      .ok ((((((Cache.raw.codes[37]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4464, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4318, limit := 4474 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4474, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4149, limit := 4474 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 18, .end), { bytes := artifactBytes, pos := 4474, limit := 4474 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4112, limit := 4474 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4474, limit := 4474 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4107, limit := 4936 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4474, limit := 4936 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4109, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 4112, limit := 4474 })
    (bodyFinish := { bytes := artifactBytes, pos := 4474, limit := 4474 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 4476, limit := 4502 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4502, limit := 4502 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4474, limit := 4936 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 4502, limit := 4936 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 4475, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 4476, limit := 4502 })
    (bodyFinish := { bytes := artifactBytes, pos := 4502, limit := 4502 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 4506, limit := 4583 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4583, limit := 4583 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 4502, limit := 4936 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 4583, limit := 4936 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 4503, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 4506, limit := 4583 })
    (bodyFinish := { bytes := artifactBytes, pos := 4583, limit := 4583 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded

end Project.EulerOutwardSpeed.Artifact
