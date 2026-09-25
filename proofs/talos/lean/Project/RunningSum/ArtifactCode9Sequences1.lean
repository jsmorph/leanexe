import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode9Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_tail54 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 15313, limit := 15632 } =
      .ok ((((raw.core.codes[9]!).body).drop 54, .end), { bytes := bytes, pos := 15632, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail50 :
    instructionSequenceAt 616 false { bytes := bytes, pos := 15144, limit := 15632 } =
      .ok ((((raw.core.codes[9]!).body).drop 50, .end), { bytes := bytes, pos := 15632, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail6 :
    instructionSequenceAt 660 false { bytes := bytes, pos := 15000, limit := 15632 } =
      .ok ((((raw.core.codes[9]!).body).drop 6, .end), { bytes := bytes, pos := 15632, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 666 false { bytes := bytes, pos := 14966, limit := 15632 } =
      .ok ((((raw.core.codes[9]!).body).drop 0, .end), { bytes := bytes, pos := 15632, limit := 15632 }) := by
  cbv


end Project.RunningSum.Artifact
