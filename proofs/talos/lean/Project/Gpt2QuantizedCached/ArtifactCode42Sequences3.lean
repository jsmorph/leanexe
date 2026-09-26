import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode42Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_tail0 :
    instructionSequenceAt 2135 false { bytes := artifactBytes, pos := 11750, limit := 13408 } =
      .ok ((((((Cache.raw.codes[42]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13321, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail99 :
    instructionSequenceAt 2137 false { bytes := artifactBytes, pos := 11748, limit := 13408 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 99, .end), { bytes := artifactBytes, pos := 13408, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail90 :
    instructionSequenceAt 2146 false { bytes := artifactBytes, pos := 11587, limit := 13408 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 90, .end), { bytes := artifactBytes, pos := 13408, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail86 :
    instructionSequenceAt 2150 false { bytes := artifactBytes, pos := 11418, limit := 13408 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 86, .end), { bytes := artifactBytes, pos := 13408, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail43 :
    instructionSequenceAt 2193 false { bytes := artifactBytes, pos := 11289, limit := 13408 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 43, .end), { bytes := artifactBytes, pos := 13408, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail0 :
    instructionSequenceAt 2236 false { bytes := artifactBytes, pos := 11172, limit := 13408 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13408, limit := 13408 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
