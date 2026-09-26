import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode3Sequences0

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_89_t_tail8 :
    instructionSequenceAt 1052 true { bytes := artifactBytes, pos := 1676, limit := 2001 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1807, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_89_t_tail0 :
    instructionSequenceAt 1060 true { bytes := artifactBytes, pos := 1663, limit := 2001 } =
      .ok ((((((Cache.raw.codes[3]!).body)[89]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1807, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_98_t_tail0 :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 1824, limit := 2001 } =
      .ok ((((((Cache.raw.codes[3]!).body)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1952, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail98 :
    instructionSequenceAt 1053 false { bytes := artifactBytes, pos := 1822, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 98, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail89 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 1661, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 89, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail85 :
    instructionSequenceAt 1066 false { bytes := artifactBytes, pos := 1492, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 85, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail42 :
    instructionSequenceAt 1109 false { bytes := artifactBytes, pos := 1260, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 42, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail33 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 1099, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 33, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
