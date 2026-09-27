import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode19Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_tail24 :
    instructionSequenceAt 1537 false { bytes := artifactBytes, pos := 6202, limit := 7717 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 24, .end), { bytes := artifactBytes, pos := 7717, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_tail0 :
    instructionSequenceAt 1561 false { bytes := artifactBytes, pos := 6156, limit := 7717 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7717, limit := 7717 }) := by
  cbv


end Project.Beck.Artifact
