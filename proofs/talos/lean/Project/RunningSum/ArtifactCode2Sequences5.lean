import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences4

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_40_t_tail14 :
    instructionSequenceAt 3782 true { bytes := bytes, pos := 3147, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[40]!).childBody false).drop 14, .end), { bytes := bytes, pos := 3275, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_40_t_tail0 :
    instructionSequenceAt 3796 true { bytes := bytes, pos := 3118, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[40]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3275, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_tail0 :
    instructionSequenceAt 3767 false { bytes := bytes, pos := 3368, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3647, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_tail0 :
    instructionSequenceAt 3742 false { bytes := bytes, pos := 3698, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4428, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_tail0 :
    instructionSequenceAt 3832 false { bytes := bytes, pos := 4501, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4780, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_tail0 :
    instructionSequenceAt 3807 false { bytes := bytes, pos := 4831, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5561, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_tail0 :
    instructionSequenceAt 3866 false { bytes := bytes, pos := 1798, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[27]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2780, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_tail94 :
    instructionSequenceAt 3744 true { bytes := bytes, pos := 3696, limit := 5631 } =
      .ok ((((((raw.core.codes[2]!).body)[55]!).childBody false).drop 94, .otherwise), { bytes := bytes, pos := 4491, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
