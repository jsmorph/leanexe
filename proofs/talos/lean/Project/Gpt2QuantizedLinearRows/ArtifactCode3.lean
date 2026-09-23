import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_29_t_0_t_tail18 :
    instructionSequenceAt 1100 false { bytes := artifactBytes, pos := 966, limit := 2002 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1094, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_0_t_tail0 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 935, limit := 2002 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1094, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail18 :
    instructionSequenceAt 1044 false { bytes := artifactBytes, pos := 1528, limit := 2002 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1656, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail0 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1497, limit := 2002 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1656, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_tail0 :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 933, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1095, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail8 :
    instructionSequenceAt 1108 true { bytes := artifactBytes, pos := 1115, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1246, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail0 :
    instructionSequenceAt 1116 true { bytes := artifactBytes, pos := 1102, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1246, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_tail0 :
    instructionSequenceAt 1064 false { bytes := artifactBytes, pos := 1495, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[85]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1657, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail8 :
    instructionSequenceAt 1052 true { bytes := artifactBytes, pos := 1677, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1808, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail0 :
    instructionSequenceAt 1060 true { bytes := artifactBytes, pos := 1664, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1808, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_98_t_tail0 :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 1825, limit := 2002 } =
      .ok ((((((Cache.raw.codes[3]!).body)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1953, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail98 :
    instructionSequenceAt 1053 false { bytes := artifactBytes, pos := 1823, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 98, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail89 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1662, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 89, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail85 :
    instructionSequenceAt 1066 false { bytes := artifactBytes, pos := 1493, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 85, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail42 :
    instructionSequenceAt 1109 false { bytes := artifactBytes, pos := 1261, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 42, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail33 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 1100, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 33, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail29 :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 931, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 29, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 1151 false { bytes := artifactBytes, pos := 851, limit := 2002 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2002, limit := 2002 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 846, limit := 4757 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 2002, limit := 4757 }) := by
  refine code_eq_of_parts (size := 1154)
    (payload := { bytes := artifactBytes, pos := 848, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 851, limit := 2002 })
    (bodyFinish := { bytes := artifactBytes, pos := 2002, limit := 2002 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
