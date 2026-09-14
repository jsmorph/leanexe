import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail1_decoded :
    instructionSequenceAt 128 false { bytes := artifactBytes, pos := 3471, limit := 3598 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 1, .end), { bytes := artifactBytes, pos := 3598, limit := 3598 }) := by
  cbv

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3469, limit := 3598 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3598, limit := 3598 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3464, limit := 7175 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3598, limit := 7175 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3466, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3469, limit := 3598 })
    (bodyFinish := { bytes := artifactBytes, pos := 3598, limit := 3598 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail30_decoded :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 3805, limit := 3810 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 30, .end), { bytes := artifactBytes, pos := 3810, limit := 3810 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3669, limit := 3810 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 29, .end), { bytes := artifactBytes, pos := 3810, limit := 3810 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3603, limit := 3810 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3810, limit := 3810 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3598, limit := 7175 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3810, limit := 7175 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3600, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3603, limit := 3810 })
    (bodyFinish := { bytes := artifactBytes, pos := 3810, limit := 3810 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 3814, limit := 3921 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3921, limit := 3921 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3810, limit := 7175 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3921, limit := 7175 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 3811, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3814, limit := 3921 })
    (bodyFinish := { bytes := artifactBytes, pos := 3921, limit := 3921 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3925, limit := 4040 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4040, limit := 4040 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3921, limit := 7175 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 4040, limit := 7175 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3922, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 3925, limit := 4040 })
    (bodyFinish := { bytes := artifactBytes, pos := 4040, limit := 4040 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 4158, limit := 4306 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4286, limit := 4306 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 4092, limit := 4306 } =
      .ok ((((((Cache.raw.codes[36]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4286, limit := 4306 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail22_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 4301, limit := 4306 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4306, limit := 4306 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 4090, limit := 4306 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4306, limit := 4306 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 4045, limit := 4306 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4306, limit := 4306 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 4040, limit := 7175 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4306, limit := 7175 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 4042, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 4045, limit := 4306 })
    (bodyFinish := { bytes := artifactBytes, pos := 4306, limit := 4306 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 4310, limit := 4359 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4359, limit := 4359 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4306, limit := 7175 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4359, limit := 7175 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 4307, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 4310, limit := 4359 })
    (bodyFinish := { bytes := artifactBytes, pos := 4359, limit := 4359 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_29_t_69_t_tail45_decoded :
    instructionSequenceAt 516 true { bytes := artifactBytes, pos := 4779, limit := 5027 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[29]!).childBody false)[69]!).childBody false).drop 45, .otherwise), { bytes := artifactBytes, pos := 4907, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_69_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 4655, limit := 5027 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[29]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4907, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail70_decoded :
    instructionSequenceAt 562 true { bytes := artifactBytes, pos := 4958, limit := 5027 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 70, .otherwise), { bytes := artifactBytes, pos := 4959, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail69_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 4653, limit := 5027 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 4959, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail57_decoded :
    instructionSequenceAt 575 true { bytes := artifactBytes, pos := 4540, limit := 5027 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 57, .otherwise), { bytes := artifactBytes, pos := 4959, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_29_t_tail0_decoded :
    instructionSequenceAt 632 true { bytes := artifactBytes, pos := 4432, limit := 5027 } =
      .ok ((((((Cache.raw.codes[38]!).body)[29]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4959, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail30_decoded :
    instructionSequenceAt 633 false { bytes := artifactBytes, pos := 5010, limit := 5027 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 30, .end), { bytes := artifactBytes, pos := 5027, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail29_decoded :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 4430, limit := 5027 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 29, .end), { bytes := artifactBytes, pos := 5027, limit := 5027 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 663 false { bytes := artifactBytes, pos := 4364, limit := 5027 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5027, limit := 5027 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4359, limit := 7175 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 5027, limit := 7175 }) := by
  refine code_eq_of_parts (size := 666)
    (payload := { bytes := artifactBytes, pos := 4361, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 4364, limit := 5027 })
    (bodyFinish := { bytes := artifactBytes, pos := 5027, limit := 5027 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5031, limit := 5038 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5038, limit := 5038 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 5027, limit := 7175 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 5038, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5028, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5031, limit := 5038 })
    (bodyFinish := { bytes := artifactBytes, pos := 5038, limit := 5038 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerOutwardFlux.Artifact
