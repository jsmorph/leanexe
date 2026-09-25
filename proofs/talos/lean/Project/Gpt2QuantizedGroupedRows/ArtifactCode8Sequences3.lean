import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode8Sequences2

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_99_t_tail0 :
    instructionSequenceAt 2133 false { bytes := artifactBytes, pos := 2924, limit := 4580 } =
      .ok ((((((Cache.raw.codes[8]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4495, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail99 :
    instructionSequenceAt 2135 false { bytes := artifactBytes, pos := 2922, limit := 4580 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 99, .end), { bytes := artifactBytes, pos := 4580, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail90 :
    instructionSequenceAt 2144 false { bytes := artifactBytes, pos := 2761, limit := 4580 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 90, .end), { bytes := artifactBytes, pos := 4580, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail86 :
    instructionSequenceAt 2148 false { bytes := artifactBytes, pos := 2592, limit := 4580 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 86, .end), { bytes := artifactBytes, pos := 4580, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail43 :
    instructionSequenceAt 2191 false { bytes := artifactBytes, pos := 2463, limit := 4580 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 43, .end), { bytes := artifactBytes, pos := 4580, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 2234 false { bytes := artifactBytes, pos := 2346, limit := 4580 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4580, limit := 4580 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
