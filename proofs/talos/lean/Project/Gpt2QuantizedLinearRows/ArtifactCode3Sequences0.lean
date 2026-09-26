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
    instructionSequenceAt 1100 false { bytes := artifactBytes, pos := 958, limit := 1994 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1086, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_0_t_tail0 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 927, limit := 1994 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1086, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail18 :
    instructionSequenceAt 1044 false { bytes := artifactBytes, pos := 1520, limit := 1994 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1648, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_0_t_tail0 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1489, limit := 1994 } =
      .ok ((((((((Cache.raw.codes[3]!).body)[85]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1648, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_29_t_tail0 :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 925, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1087, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail8 :
    instructionSequenceAt 1108 true { bytes := artifactBytes, pos := 1107, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1238, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_33_t_tail0 :
    instructionSequenceAt 1116 true { bytes := artifactBytes, pos := 1094, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1238, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_85_t_tail0 :
    instructionSequenceAt 1064 false { bytes := artifactBytes, pos := 1487, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[85]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1649, limit := 1994 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
