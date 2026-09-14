import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4334, limit := 4341 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4341, limit := 4341 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 4330, limit := 5728 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 4341, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4331, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4334, limit := 4341 })
    (bodyFinish := { bytes := artifactBytes, pos := 4341, limit := 4341 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4345, limit := 4352 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4352, limit := 4352 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 4341, limit := 5728 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 4352, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4342, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4345, limit := 4352 })
    (bodyFinish := { bytes := artifactBytes, pos := 4352, limit := 4352 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 103 false { bytes := artifactBytes, pos := 4356, limit := 4459 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4459, limit := 4459 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 4352, limit := 5728 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 4459, limit := 5728 }) := by
  refine code_eq_of_parts (size := 106)
    (payload := { bytes := artifactBytes, pos := 4353, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4356, limit := 4459 })
    (bodyFinish := { bytes := artifactBytes, pos := 4459, limit := 4459 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 4463, limit := 4488 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4488, limit := 4488 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 4459, limit := 5728 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 4488, limit := 5728 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 4460, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4463, limit := 4488 })
    (bodyFinish := { bytes := artifactBytes, pos := 4488, limit := 4488 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 4492, limit := 4565 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4565, limit := 4565 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 4488, limit := 5728 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 4565, limit := 5728 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 4489, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4492, limit := 4565 })
    (bodyFinish := { bytes := artifactBytes, pos := 4565, limit := 4565 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_25_t_0_t_tail77_decoded :
    instructionSequenceAt 223 false { bytes := artifactBytes, pos := 4758, limit := 4899 } =
      .ok ((((((((Cache.raw.codes[45]!).body)[25]!).childBody false)[0]!).childBody false).drop 77, .end), { bytes := artifactBytes, pos := 4885, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_25_t_0_t_tail1_decoded :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 4631, limit := 4899 } =
      .ok ((((((((Cache.raw.codes[45]!).body)[25]!).childBody false)[0]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 4885, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_25_t_0_t_tail0_decoded :
    instructionSequenceAt 300 false { bytes := artifactBytes, pos := 4629, limit := 4899 } =
      .ok ((((((((Cache.raw.codes[45]!).body)[25]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4885, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_25_t_tail1_decoded :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 4885, limit := 4899 } =
      .ok ((((((Cache.raw.codes[45]!).body)[25]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 4886, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_25_t_tail0_decoded :
    instructionSequenceAt 302 false { bytes := artifactBytes, pos := 4627, limit := 4899 } =
      .ok ((((((Cache.raw.codes[45]!).body)[25]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4886, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail26_decoded :
    instructionSequenceAt 303 false { bytes := artifactBytes, pos := 4886, limit := 4899 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 26, .end), { bytes := artifactBytes, pos := 4899, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail25_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 4625, limit := 4899 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 25, .end), { bytes := artifactBytes, pos := 4899, limit := 4899 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 329 false { bytes := artifactBytes, pos := 4570, limit := 4899 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4899, limit := 4899 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 4565, limit := 5728 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 4899, limit := 5728 }) := by
  refine code_eq_of_parts (size := 332)
    (payload := { bytes := artifactBytes, pos := 4567, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4570, limit := 4899 })
    (bodyFinish := { bytes := artifactBytes, pos := 4899, limit := 4899 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_seq_46_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4976, limit := 5266 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 5104, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4945, limit := 5266 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5104, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_18_t_tail1_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 5104, limit := 5266 } =
      .ok ((((((Cache.raw.codes[46]!).body)[18]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 5105, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4943, limit := 5266 } =
      .ok ((((((Cache.raw.codes[46]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5105, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_22_t_tail9_decoded :
    instructionSequenceAt 329 true { bytes := artifactBytes, pos := 5129, limit := 5266 } =
      .ok ((((((Cache.raw.codes[46]!).body)[22]!).childBody false).drop 9, .end), { bytes := artifactBytes, pos := 5256, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 5112, limit := 5266 } =
      .ok ((((((Cache.raw.codes[46]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5256, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail23_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 5256, limit := 5266 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 23, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 5110, limit := 5266 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 22, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail19_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 5105, limit := 5266 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 19, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4941, limit := 5266 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 18, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4904, limit := 5266 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 4899, limit := 5728 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 5266, limit := 5728 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4901, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4904, limit := 5266 })
    (bodyFinish := { bytes := artifactBytes, pos := 5266, limit := 5266 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_seq_47_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 5268, limit := 5294 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5294, limit := 5294 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 5266, limit := 5728 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 5294, limit := 5728 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 5267, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 5268, limit := 5294 })
    (bodyFinish := { bytes := artifactBytes, pos := 5294, limit := 5294 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_seq_47_tail0_decoded
  · rfl

#print axioms code47_decoded


end Project.EulerOutwardGrid.Artifact
