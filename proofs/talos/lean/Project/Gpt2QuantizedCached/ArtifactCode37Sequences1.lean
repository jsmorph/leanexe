import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode37Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_89_t_tail8 :
    instructionSequenceAt 1052 true { bytes := artifactBytes, pos := 10502, limit := 10827 } =
      .ok ((((((Cache.raw.codes[37]!).body)[89]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10633, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_89_t_tail0 :
    instructionSequenceAt 1060 true { bytes := artifactBytes, pos := 10489, limit := 10827 } =
      .ok ((((((Cache.raw.codes[37]!).body)[89]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10633, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_98_t_tail0 :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 10650, limit := 10827 } =
      .ok ((((((Cache.raw.codes[37]!).body)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10778, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail98 :
    instructionSequenceAt 1053 false { bytes := artifactBytes, pos := 10648, limit := 10827 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 98, .end), { bytes := artifactBytes, pos := 10827, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail89 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 10487, limit := 10827 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 89, .end), { bytes := artifactBytes, pos := 10827, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail85 :
    instructionSequenceAt 1066 false { bytes := artifactBytes, pos := 10318, limit := 10827 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 85, .end), { bytes := artifactBytes, pos := 10827, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail42 :
    instructionSequenceAt 1109 false { bytes := artifactBytes, pos := 10086, limit := 10827 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 42, .end), { bytes := artifactBytes, pos := 10827, limit := 10827 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail33 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 9925, limit := 10827 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 33, .end), { bytes := artifactBytes, pos := 10827, limit := 10827 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
