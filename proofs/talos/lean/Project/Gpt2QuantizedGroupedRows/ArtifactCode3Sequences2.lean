import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode3Sequences1

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail29 :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 930, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 29, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 1151 false { bytes := artifactBytes, pos := 850, limit := 2001 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2001, limit := 2001 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
