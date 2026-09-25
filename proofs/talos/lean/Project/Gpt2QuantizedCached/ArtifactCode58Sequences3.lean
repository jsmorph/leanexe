import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode58Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_tail0 :
    instructionSequenceAt 2070 false { bytes := artifactBytes, pos := 23680, limit := 25750 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 25750, limit := 25750 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
