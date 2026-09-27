import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences9

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_tail0 :
    instructionSequenceAt 4714 false { bytes := artifactBytes, pos := 14019, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
