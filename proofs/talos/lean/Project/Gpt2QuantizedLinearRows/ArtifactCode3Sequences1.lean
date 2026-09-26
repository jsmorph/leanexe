import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode3Sequences0

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_89_t_tail8 :
    instructionSequenceAt 1052 true { bytes := artifactBytes, pos := 1669, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1800, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail0 :
    instructionSequenceAt 1060 true { bytes := artifactBytes, pos := 1656, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1800, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_98_t_tail0 :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 1817, limit := 1994 } =
      .ok ((((((Cache.raw.codes[3]!).body)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1945, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail98 :
    instructionSequenceAt 1053 false { bytes := artifactBytes, pos := 1815, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 98, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail89 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1654, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 89, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail85 :
    instructionSequenceAt 1066 false { bytes := artifactBytes, pos := 1485, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 85, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail42 :
    instructionSequenceAt 1109 false { bytes := artifactBytes, pos := 1253, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 42, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail33 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 1092, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 33, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
