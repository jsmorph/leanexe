import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5042, limit := 5049 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5049, limit := 5049 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 5038, limit := 7175 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5049, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5039, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5042, limit := 5049 })
    (bodyFinish := { bytes := artifactBytes, pos := 5049, limit := 5049 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 5053, limit := 5091 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5091, limit := 5091 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 5049, limit := 7175 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5091, limit := 7175 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 5050, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5053, limit := 5091 })
    (bodyFinish := { bytes := artifactBytes, pos := 5091, limit := 5091 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 5095, limit := 5114 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5114, limit := 5114 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5091, limit := 7175 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5114, limit := 7175 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 5092, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5095, limit := 5114 })
    (bodyFinish := { bytes := artifactBytes, pos := 5114, limit := 5114 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 5118, limit := 5151 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5151, limit := 5151 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5114, limit := 7175 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5151, limit := 7175 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 5115, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5118, limit := 5151 })
    (bodyFinish := { bytes := artifactBytes, pos := 5151, limit := 5151 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 5155, limit := 5168 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5168, limit := 5168 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5151, limit := 7175 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5168, limit := 7175 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 5152, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5155, limit := 5168 })
    (bodyFinish := { bytes := artifactBytes, pos := 5168, limit := 5168 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_18_t_tail50_decoded :
    instructionSequenceAt 287 true { bytes := artifactBytes, pos := 5388, limit := 5530 } =
      .ok ((((((Cache.raw.codes[45]!).body)[18]!).childBody false).drop 50, .otherwise), { bytes := artifactBytes, pos := 5510, limit := 5530 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_18_t_tail0_decoded :
    instructionSequenceAt 337 true { bytes := artifactBytes, pos := 5282, limit := 5530 } =
      .ok ((((((Cache.raw.codes[45]!).body)[18]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5510, limit := 5530 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail19_decoded :
    instructionSequenceAt 338 false { bytes := artifactBytes, pos := 5525, limit := 5530 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 19, .end), { bytes := artifactBytes, pos := 5530, limit := 5530 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail18_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 5280, limit := 5530 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 18, .end), { bytes := artifactBytes, pos := 5530, limit := 5530 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 5173, limit := 5530 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5530, limit := 5530 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 5168, limit := 7175 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 5530, limit := 7175 }) := by
  refine code_eq_of_parts (size := 360)
    (payload := { bytes := artifactBytes, pos := 5170, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5173, limit := 5530 })
    (bodyFinish := { bytes := artifactBytes, pos := 5530, limit := 5530 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 5534, limit := 5583 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5583, limit := 5583 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 5530, limit := 7175 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 5583, limit := 7175 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 5531, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5534, limit := 5583 })
    (bodyFinish := { bytes := artifactBytes, pos := 5583, limit := 5583 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_seq_47_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5587, limit := 5594 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5594, limit := 5594 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 5583, limit := 7175 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 5594, limit := 7175 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5584, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 5587, limit := 5594 })
    (bodyFinish := { bytes := artifactBytes, pos := 5594, limit := 5594 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_seq_47_tail0_decoded
  · rfl

#print axioms code47_decoded


end Project.EulerOutwardFlux.Artifact
