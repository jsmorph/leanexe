import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_29_t_0_t_tail18 :
    instructionSequenceAt 1100 false { bytes := artifactBytes, pos := 973, limit := 2009 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1101, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_0_t_tail0 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 942, limit := 2009 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1101, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail18 :
    instructionSequenceAt 1044 false { bytes := artifactBytes, pos := 1535, limit := 2009 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1663, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail0 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1504, limit := 2009 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1663, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_tail0 :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 940, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1102, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail8 :
    instructionSequenceAt 1108 true { bytes := artifactBytes, pos := 1122, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1253, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail0 :
    instructionSequenceAt 1116 true { bytes := artifactBytes, pos := 1109, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1253, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_tail0 :
    instructionSequenceAt 1064 false { bytes := artifactBytes, pos := 1502, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[85]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1664, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail8 :
    instructionSequenceAt 1052 true { bytes := artifactBytes, pos := 1684, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1815, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail0 :
    instructionSequenceAt 1060 true { bytes := artifactBytes, pos := 1671, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1815, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_98_t_tail0 :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 1832, limit := 2009 } =
      .ok ((((((Cache.raw.codes[3]!).body)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1960, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail98 :
    instructionSequenceAt 1053 false { bytes := artifactBytes, pos := 1830, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 98, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail89 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1669, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 89, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail85 :
    instructionSequenceAt 1066 false { bytes := artifactBytes, pos := 1500, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 85, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail42 :
    instructionSequenceAt 1109 false { bytes := artifactBytes, pos := 1268, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 42, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail33 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 1107, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 33, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail29 :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 938, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 29, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 1151 false { bytes := artifactBytes, pos := 858, limit := 2009 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2009, limit := 2009 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 853, limit := 5441 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 2009, limit := 5441 }) := by
  refine code_eq_of_parts (size := 1154)
    (payload := { bytes := artifactBytes, pos := 855, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 858, limit := 2009 })
    (bodyFinish := { bytes := artifactBytes, pos := 2009, limit := 2009 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
