import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 4650, limit := 4758 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4758, limit := 4758 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 4646, limit := 30726 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 4758, limit := 30726 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 4647, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4650, limit := 4758 })
    (bodyFinish := { bytes := artifactBytes, pos := 4758, limit := 4758 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 4762, limit := 4877 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4877, limit := 4877 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 4758, limit := 30726 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 4877, limit := 30726 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 4759, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4762, limit := 4877 })
    (bodyFinish := { bytes := artifactBytes, pos := 4877, limit := 4877 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 4882, limit := 5011 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5011, limit := 5011 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 4877, limit := 30726 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 5011, limit := 30726 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 4879, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 4882, limit := 5011 })
    (bodyFinish := { bytes := artifactBytes, pos := 5011, limit := 5011 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 5082, limit := 5223 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 29, .end), { bytes := artifactBytes, pos := 5223, limit := 5223 }) := by
  cbv

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 5016, limit := 5223 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5223, limit := 5223 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 5011, limit := 30726 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 5223, limit := 30726 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 5013, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5016, limit := 5223 })
    (bodyFinish := { bytes := artifactBytes, pos := 5223, limit := 5223 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 5227, limit := 5334 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5334, limit := 5334 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 5223, limit := 30726 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 5334, limit := 30726 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 5224, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5227, limit := 5334 })
    (bodyFinish := { bytes := artifactBytes, pos := 5334, limit := 5334 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 5338, limit := 5453 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5453, limit := 5453 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 5334, limit := 30726 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 5453, limit := 30726 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 5335, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5338, limit := 5453 })
    (bodyFinish := { bytes := artifactBytes, pos := 5453, limit := 5453 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 5571, limit := 5719 } =
      .ok ((((((Cache.raw.codes[38]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 5699, limit := 5719 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 5505, limit := 5719 } =
      .ok ((((((Cache.raw.codes[38]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5699, limit := 5719 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 5503, limit := 5719 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 21, .end), { bytes := artifactBytes, pos := 5719, limit := 5719 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 5458, limit := 5719 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5719, limit := 5719 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 5453, limit := 30726 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 5719, limit := 30726 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 5455, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5458, limit := 5719 })
    (bodyFinish := { bytes := artifactBytes, pos := 5719, limit := 5719 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5723, limit := 5730 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5730, limit := 5730 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 5719, limit := 30726 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 5730, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5720, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5723, limit := 5730 })
    (bodyFinish := { bytes := artifactBytes, pos := 5730, limit := 5730 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerReconstructed.Artifact
