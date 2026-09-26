import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences4

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_tail0 :
    instructionSequenceAt 4482 false { bytes := bytes, pos := 10511, limit := 14961 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 14791, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_tail0 :
    instructionSequenceAt 4484 false { bytes := bytes, pos := 10509, limit := 14961 } =
      .ok ((((((raw.core.codes[8]!).body)[32]!).childBody false).drop 0, .end), { bytes := bytes, pos := 14792, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail49 :
    instructionSequenceAt 4469 false { bytes := bytes, pos := 14832, limit := 14961 } =
      .ok ((((raw.core.codes[8]!).body).drop 49, .end), { bytes := bytes, pos := 14961, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail32 :
    instructionSequenceAt 4486 false { bytes := bytes, pos := 10507, limit := 14961 } =
      .ok ((((raw.core.codes[8]!).body).drop 32, .end), { bytes := bytes, pos := 14961, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 4518 false { bytes := bytes, pos := 10443, limit := 14961 } =
      .ok ((((raw.core.codes[8]!).body).drop 0, .end), { bytes := bytes, pos := 14961, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
