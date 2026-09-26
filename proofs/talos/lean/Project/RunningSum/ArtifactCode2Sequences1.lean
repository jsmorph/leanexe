import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_75_t_tail0 :
    instructionSequenceAt 3663 true { bytes := bytes, pos := 4074, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4233, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_71_t_tail0 :
    instructionSequenceAt 3732 false { bytes := bytes, pos := 5012, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[71]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5199, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_75_t_tail14 :
    instructionSequenceAt 3714 true { bytes := bytes, pos := 5237, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 14, .end), { bytes := bytes, pos := 5366, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_75_t_tail0 :
    instructionSequenceAt 3728 true { bytes := bytes, pos := 5207, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5366, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_74_t_tail0 :
    instructionSequenceAt 3788 false { bytes := bytes, pos := 2157, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[74]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2344, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_78_t_tail14 :
    instructionSequenceAt 3770 true { bytes := bytes, pos := 2382, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 14, .end), { bytes := bytes, pos := 2511, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_78_t_tail0 :
    instructionSequenceAt 3784 true { bytes := bytes, pos := 2352, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[78]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2511, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_36_t_0_t_tail20 :
    instructionSequenceAt 3778 false { bytes := bytes, pos := 2980, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false)[0]!).childBody false).drop 20, .end), { bytes := bytes, pos := 3109, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
