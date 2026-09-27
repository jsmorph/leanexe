import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences6

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail27 :
    instructionSequenceAt 3868 false { bytes := bytes, pos := 1796, limit := 5631 } =
      .ok ((((raw.core.codes[2]!).body).drop 27, .end), { bytes := bytes, pos := 5631, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 3895 false { bytes := bytes, pos := 1736, limit := 5631 } =
      .ok ((((raw.core.codes[2]!).body).drop 0, .end), { bytes := bytes, pos := 5631, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
