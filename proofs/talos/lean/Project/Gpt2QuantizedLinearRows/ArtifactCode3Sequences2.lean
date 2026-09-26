import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode3Sequences1

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail29 :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 923, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 29, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 1151 false { bytes := artifactBytes, pos := 843, limit := 1994 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1994, limit := 1994 }) := by
  cbv


end Project.Gpt2QuantizedLinearRows.Artifact
