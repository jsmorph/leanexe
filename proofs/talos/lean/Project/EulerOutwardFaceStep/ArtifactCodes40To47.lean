import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5256, limit := 5263 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5263, limit := 5263 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 5252, limit := 9077 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5263, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5253, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5256, limit := 5263 })
    (bodyFinish := { bytes := artifactBytes, pos := 5263, limit := 5263 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 5267, limit := 5305 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5305, limit := 5305 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 5263, limit := 9077 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5305, limit := 9077 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 5264, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5267, limit := 5305 })
    (bodyFinish := { bytes := artifactBytes, pos := 5305, limit := 5305 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 5309, limit := 5328 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5328, limit := 5328 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5305, limit := 9077 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5328, limit := 9077 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 5306, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5309, limit := 5328 })
    (bodyFinish := { bytes := artifactBytes, pos := 5328, limit := 5328 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 5332, limit := 5365 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5365, limit := 5365 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5328, limit := 9077 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5365, limit := 9077 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 5329, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5332, limit := 5365 })
    (bodyFinish := { bytes := artifactBytes, pos := 5365, limit := 5365 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 5369, limit := 5382 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5382, limit := 5382 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5365, limit := 9077 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5382, limit := 9077 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 5366, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5369, limit := 5382 })
    (bodyFinish := { bytes := artifactBytes, pos := 5382, limit := 5382 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_18_t_tail50_decoded :
    instructionSequenceAt 287 true { bytes := artifactBytes, pos := 5602, limit := 5744 } =
      .ok ((((((Cache.raw.codes[45]!).body)[18]!).childBody false).drop 50, .otherwise), { bytes := artifactBytes, pos := 5724, limit := 5744 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_18_t_tail0_decoded :
    instructionSequenceAt 337 true { bytes := artifactBytes, pos := 5496, limit := 5744 } =
      .ok ((((((Cache.raw.codes[45]!).body)[18]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5724, limit := 5744 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail19_decoded :
    instructionSequenceAt 338 false { bytes := artifactBytes, pos := 5739, limit := 5744 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 19, .end), { bytes := artifactBytes, pos := 5744, limit := 5744 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail18_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 5494, limit := 5744 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 18, .end), { bytes := artifactBytes, pos := 5744, limit := 5744 }) := by
  cbv

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 5387, limit := 5744 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5744, limit := 5744 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 5382, limit := 9077 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 5744, limit := 9077 }) := by
  refine code_eq_of_parts (size := 360)
    (payload := { bytes := artifactBytes, pos := 5384, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5387, limit := 5744 })
    (bodyFinish := { bytes := artifactBytes, pos := 5744, limit := 5744 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 5748, limit := 5797 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5797, limit := 5797 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 5744, limit := 9077 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 5797, limit := 9077 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 5745, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5748, limit := 5797 })
    (bodyFinish := { bytes := artifactBytes, pos := 5797, limit := 5797 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_seq_47_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5801, limit := 5808 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5808, limit := 5808 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 5797, limit := 9077 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 5808, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5798, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5801, limit := 5808 })
    (bodyFinish := { bytes := artifactBytes, pos := 5808, limit := 5808 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_seq_47_tail0_decoded
  · rfl

#print axioms code47_decoded


end Project.EulerOutwardFaceStep.Artifact
