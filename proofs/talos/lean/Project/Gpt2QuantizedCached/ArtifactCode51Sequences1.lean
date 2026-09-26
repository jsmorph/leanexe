import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode51Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_51_tail0 :
    instructionSequenceAt 552 false { bytes := artifactBytes, pos := 19379, limit := 19931 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19931, limit := 19931 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
