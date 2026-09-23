import Project.Gpt2QuantizedCached.ArtifactCode58Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_tail114 :
    instructionSequenceAt 2118 false { bytes := artifactBytes, pos := 25913, limit := 26048 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 114, .end), { bytes := artifactBytes, pos := 26048, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_tail107 :
    instructionSequenceAt 2125 false { bytes := artifactBytes, pos := 25252, limit := 26048 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 107, .end), { bytes := artifactBytes, pos := 26048, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_tail59 :
    instructionSequenceAt 2173 false { bytes := artifactBytes, pos := 23937, limit := 26048 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 59, .end), { bytes := artifactBytes, pos := 26048, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_tail0 :
    instructionSequenceAt 2232 false { bytes := artifactBytes, pos := 23816, limit := 26048 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26048, limit := 26048 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
