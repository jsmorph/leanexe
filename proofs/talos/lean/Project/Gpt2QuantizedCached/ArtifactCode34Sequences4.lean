import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode34Sequences3

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_tail42 :
    instructionSequenceAt 2085 false { bytes := artifactBytes, pos := 7510, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 42, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail33 :
    instructionSequenceAt 2094 false { bytes := artifactBytes, pos := 7349, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 33, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail29 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 7180, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 29, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail0 :
    instructionSequenceAt 2127 false { bytes := artifactBytes, pos := 7100, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
