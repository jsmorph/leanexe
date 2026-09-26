import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode4Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail15 :
    instructionSequenceAt 699 false { bytes := bytes, pos := 5700, limit := 6373 } =
      .ok ((((raw.core.codes[4]!).body).drop 15, .end), { bytes := bytes, pos := 6373, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 714 false { bytes := bytes, pos := 5659, limit := 6373 } =
      .ok ((((raw.core.codes[4]!).body).drop 0, .end), { bytes := bytes, pos := 6373, limit := 6373 }) := by
  cbv


end Project.RunningSum.Artifact
