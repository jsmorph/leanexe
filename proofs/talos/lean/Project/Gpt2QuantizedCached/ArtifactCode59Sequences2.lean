import Project.Gpt2QuantizedCached.ArtifactCode59Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_59_tail0 :
    instructionSequenceAt 1362 false { bytes := artifactBytes, pos := 26053, limit := 27415 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27415, limit := 27415 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
