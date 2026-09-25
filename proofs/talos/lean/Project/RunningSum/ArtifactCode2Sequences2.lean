import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_36_t_0_t_tail0 :
    instructionSequenceAt 3798 false { bytes := bytes, pos := 2941, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3109, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail15 :
    instructionSequenceAt 3750 false { bytes := bytes, pos := 3517, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := bytes, pos := 3646, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail5 :
    instructionSequenceAt 3760 false { bytes := bytes, pos := 3379, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 5, .end), { bytes := bytes, pos := 3646, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_69_t_0_t_tail0 :
    instructionSequenceAt 3765 false { bytes := bytes, pos := 3370, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[69]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3646, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail91 :
    instructionSequenceAt 3649 false { bytes := bytes, pos := 4298, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 91, .end), { bytes := bytes, pos := 4427, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail75 :
    instructionSequenceAt 3665 false { bytes := bytes, pos := 4072, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := bytes, pos := 4427, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail71 :
    instructionSequenceAt 3669 false { bytes := bytes, pos := 3877, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 71, .end), { bytes := bytes, pos := 4427, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail21 :
    instructionSequenceAt 3719 false { bytes := bytes, pos := 3742, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := bytes, pos := 4427, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
