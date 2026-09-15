import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail1_decoded :
    instructionSequenceAt 128 false { bytes := artifactBytes, pos := 3685, limit := 3812 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 1, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3683, limit := 3812 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3678, limit := 9077 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3812, limit := 9077 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3680, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3683, limit := 3812 })
    (bodyFinish := { bytes := artifactBytes, pos := 3812, limit := 3812 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail30_decoded :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 4019, limit := 4024 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 30, .end), { bytes := artifactBytes, pos := 4024, limit := 4024 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3883, limit := 4024 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 29, .end), { bytes := artifactBytes, pos := 4024, limit := 4024 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3817, limit := 4024 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4024, limit := 4024 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3812, limit := 9077 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 4024, limit := 9077 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3814, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 3817, limit := 4024 })
    (bodyFinish := { bytes := artifactBytes, pos := 4024, limit := 4024 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 4028, limit := 4135 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4135, limit := 4135 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 4024, limit := 9077 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 4135, limit := 9077 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 4025, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 4028, limit := 4135 })
    (bodyFinish := { bytes := artifactBytes, pos := 4135, limit := 4135 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 4139, limit := 4254 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4254, limit := 4254 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 4135, limit := 9077 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 4254, limit := 9077 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 4136, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 4139, limit := 4254 })
    (bodyFinish := { bytes := artifactBytes, pos := 4254, limit := 4254 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 4372, limit := 4520 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4500, limit := 4520 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 4306, limit := 4520 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4500, limit := 4520 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail22_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 4515, limit := 4520 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4520, limit := 4520 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 4304, limit := 4520 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4520, limit := 4520 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 4259, limit := 4520 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4520, limit := 4520 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 4254, limit := 9077 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4520, limit := 9077 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 4256, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 4259, limit := 4520 })
    (bodyFinish := { bytes := artifactBytes, pos := 4520, limit := 4520 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 4524, limit := 4573 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4573, limit := 4573 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4520, limit := 9077 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4573, limit := 9077 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 4521, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 4524, limit := 4573 })
    (bodyFinish := { bytes := artifactBytes, pos := 4573, limit := 4573 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_29_t_69_t_tail45_decoded :
    instructionSequenceAt 516 true { bytes := artifactBytes, pos := 4993, limit := 5241 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[29]!).childBody false)[69]!).childBody false).drop 45, .otherwise), { bytes := artifactBytes, pos := 5121, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_69_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 4869, limit := 5241 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[29]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5121, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail70_decoded :
    instructionSequenceAt 562 true { bytes := artifactBytes, pos := 5172, limit := 5241 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 70, .otherwise), { bytes := artifactBytes, pos := 5173, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail69_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 4867, limit := 5241 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 5173, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail57_decoded :
    instructionSequenceAt 575 true { bytes := artifactBytes, pos := 4754, limit := 5241 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 57, .otherwise), { bytes := artifactBytes, pos := 5173, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail0_decoded :
    instructionSequenceAt 632 true { bytes := artifactBytes, pos := 4646, limit := 5241 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5173, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail30_decoded :
    instructionSequenceAt 633 false { bytes := artifactBytes, pos := 5224, limit := 5241 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 30, .end), { bytes := artifactBytes, pos := 5241, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail29_decoded :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 4644, limit := 5241 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 29, .end), { bytes := artifactBytes, pos := 5241, limit := 5241 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 663 false { bytes := artifactBytes, pos := 4578, limit := 5241 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5241, limit := 5241 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4573, limit := 9077 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 5241, limit := 9077 }) := by
  refine code_eq_of_parts (size := 666)
    (payload := { bytes := artifactBytes, pos := 4575, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 4578, limit := 5241 })
    (bodyFinish := { bytes := artifactBytes, pos := 5241, limit := 5241 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5245, limit := 5252 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5252, limit := 5252 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 5241, limit := 9077 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 5252, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5242, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5245, limit := 5252 })
    (bodyFinish := { bytes := artifactBytes, pos := 5252, limit := 5252 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerOutwardFaceStep.Artifact
