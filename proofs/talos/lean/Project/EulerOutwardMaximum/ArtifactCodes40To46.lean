import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4306, limit := 4313 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4313, limit := 4313 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 4302, limit := 5260 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 4313, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4303, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4306, limit := 4313 })
    (bodyFinish := { bytes := artifactBytes, pos := 4313, limit := 4313 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4317, limit := 4324 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4324, limit := 4324 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 4313, limit := 5260 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 4324, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4314, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4317, limit := 4324 })
    (bodyFinish := { bytes := artifactBytes, pos := 4324, limit := 4324 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 103 false { bytes := artifactBytes, pos := 4328, limit := 4431 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4431, limit := 4431 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 4324, limit := 5260 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 4431, limit := 5260 }) := by
  refine code_eq_of_parts (size := 106)
    (payload := { bytes := artifactBytes, pos := 4325, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4328, limit := 4431 })
    (bodyFinish := { bytes := artifactBytes, pos := 4431, limit := 4431 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4508, limit := 4798 } =
      .ok ((((((((Cache.raw.codes[43]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4636, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4477, limit := 4798 } =
      .ok ((((((((Cache.raw.codes[43]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4636, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_18_t_tail1_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 4636, limit := 4798 } =
      .ok ((((((Cache.raw.codes[43]!).body)[18]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 4637, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4475, limit := 4798 } =
      .ok ((((((Cache.raw.codes[43]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4637, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_22_t_tail9_decoded :
    instructionSequenceAt 329 true { bytes := artifactBytes, pos := 4661, limit := 4798 } =
      .ok ((((((Cache.raw.codes[43]!).body)[22]!).childBody false).drop 9, .end), { bytes := artifactBytes, pos := 4788, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 4644, limit := 4798 } =
      .ok ((((((Cache.raw.codes[43]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4788, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail23_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 4788, limit := 4798 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 23, .end), { bytes := artifactBytes, pos := 4798, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4642, limit := 4798 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4798, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail19_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 4637, limit := 4798 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 19, .end), { bytes := artifactBytes, pos := 4798, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4473, limit := 4798 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 18, .end), { bytes := artifactBytes, pos := 4798, limit := 4798 }) := by
  cbv

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4436, limit := 4798 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4798, limit := 4798 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 4431, limit := 5260 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 4798, limit := 5260 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4433, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4436, limit := 4798 })
    (bodyFinish := { bytes := artifactBytes, pos := 4798, limit := 4798 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 4800, limit := 4826 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4826, limit := 4826 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 4798, limit := 5260 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 4826, limit := 5260 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 4799, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4800, limit := 4826 })
    (bodyFinish := { bytes := artifactBytes, pos := 4826, limit := 4826 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 4830, limit := 4907 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4907, limit := 4907 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 4826, limit := 5260 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 4907, limit := 5260 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 4827, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4830, limit := 4907 })
    (bodyFinish := { bytes := artifactBytes, pos := 4907, limit := 4907 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_seq_46_tail44_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 5226, limit := 5260 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 44, .end), { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail42_decoded :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 5099, limit := 5260 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 42, .end), { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 4971, limit := 5260 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 25, .end), { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 4912, limit := 5260 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 4907, limit := 5260 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 4909, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4912, limit := 5260 })
    (bodyFinish := { bytes := artifactBytes, pos := 5260, limit := 5260 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded


end Project.EulerOutwardMaximum.Artifact
