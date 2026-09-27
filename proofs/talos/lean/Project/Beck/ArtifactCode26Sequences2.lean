import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode26Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_tail35 :
    instructionSequenceAt 1870 false { bytes := artifactBytes, pos := 11009, limit := 12826 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 35, .end), { bytes := artifactBytes, pos := 12826, limit := 12826 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail0 :
    instructionSequenceAt 1905 false { bytes := artifactBytes, pos := 10921, limit := 12826 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12826, limit := 12826 }) := by
  cbv


end Project.Beck.Artifact
