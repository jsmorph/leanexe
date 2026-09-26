import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences6

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_tail0 :
    instructionSequenceAt 3318 false { bytes := bytes, pos := 7622, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10006, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail10 :
    instructionSequenceAt 3320 false { bytes := bytes, pos := 6711, limit := 10013 } =
      .ok ((((raw.core.codes[6]!).body).drop 10, .end), { bytes := bytes, pos := 10013, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 3330 false { bytes := bytes, pos := 6683, limit := 10013 } =
      .ok ((((raw.core.codes[6]!).body).drop 0, .end), { bytes := bytes, pos := 10013, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
