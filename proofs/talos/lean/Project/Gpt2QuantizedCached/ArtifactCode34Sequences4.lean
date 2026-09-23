import Project.Gpt2QuantizedCached.ArtifactCode34Sequences3
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_tail42 :
    instructionSequenceAt 2093 false { bytes := artifactBytes, pos := 7558, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 42, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail33 :
    instructionSequenceAt 2102 false { bytes := artifactBytes, pos := 7397, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 33, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail29 :
    instructionSequenceAt 2106 false { bytes := artifactBytes, pos := 7228, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 29, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail0 :
    instructionSequenceAt 2135 false { bytes := artifactBytes, pos := 7148, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
