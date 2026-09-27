import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode2Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail6 :
    instructionSequenceAt 957 false { bytes := artifactBytes, pos := 1074, limit := 2025 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 6, .end), { bytes := artifactBytes, pos := 2025, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 963 false { bytes := artifactBytes, pos := 1062, limit := 2025 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2025, limit := 2025 }) := by
  cbv


end Project.Beck.Artifact
