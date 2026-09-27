import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode27Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_27_tail8 :
    instructionSequenceAt 640 false { bytes := artifactBytes, pos := 12847, limit := 13479 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 8, .end), { bytes := artifactBytes, pos := 13479, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail0 :
    instructionSequenceAt 648 false { bytes := artifactBytes, pos := 12831, limit := 13479 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13479, limit := 13479 }) := by
  cbv


end Project.Beck.Artifact
