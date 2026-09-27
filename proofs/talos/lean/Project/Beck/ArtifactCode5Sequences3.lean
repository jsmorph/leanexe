import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode5Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_6_t_0_t_tail0 :
    instructionSequenceAt 1610 false { bytes := artifactBytes, pos := 2074, limit := 3678 } =
      .ok ((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3637, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_tail0 :
    instructionSequenceAt 1612 false { bytes := artifactBytes, pos := 2072, limit := 3678 } =
      .ok ((((((Cache.raw.codes[5]!).body)[6]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3638, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail6 :
    instructionSequenceAt 1614 false { bytes := artifactBytes, pos := 2070, limit := 3678 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 6, .end), { bytes := artifactBytes, pos := 3678, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 1620 false { bytes := artifactBytes, pos := 2058, limit := 3678 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3678, limit := 3678 }) := by
  cbv


end Project.Beck.Artifact
