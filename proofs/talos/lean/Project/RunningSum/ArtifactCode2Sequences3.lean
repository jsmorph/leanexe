import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences2

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_tail0 :
    instructionSequenceAt 3740 false { bytes := bytes, pos := 3700, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4427, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail15 :
    instructionSequenceAt 3815 false { bytes := bytes, pos := 4650, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := bytes, pos := 4779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail5 :
    instructionSequenceAt 3825 false { bytes := bytes, pos := 4512, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 5, .end), { bytes := bytes, pos := 4779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_4_t_0_t_tail0 :
    instructionSequenceAt 3830 false { bytes := bytes, pos := 4503, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail91 :
    instructionSequenceAt 3714 false { bytes := bytes, pos := 5431, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 91, .end), { bytes := bytes, pos := 5560, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail75 :
    instructionSequenceAt 3730 false { bytes := bytes, pos := 5205, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := bytes, pos := 5560, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail71 :
    instructionSequenceAt 3734 false { bytes := bytes, pos := 5010, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 71, .end), { bytes := bytes, pos := 5560, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail21 :
    instructionSequenceAt 3784 false { bytes := bytes, pos := 4875, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := bytes, pos := 5560, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
