import Project.Gpt2QuantizedCached.ArtifactCode37Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_tail29 :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 9820, limit := 10891 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 29, .end), { bytes := artifactBytes, pos := 10891, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail0 :
    instructionSequenceAt 1151 false { bytes := artifactBytes, pos := 9740, limit := 10891 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10891, limit := 10891 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
