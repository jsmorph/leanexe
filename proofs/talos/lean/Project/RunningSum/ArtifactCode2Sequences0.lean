import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_71_t_0_t_tail23 :
    instructionSequenceAt 3642 false { bytes := bytes, pos := 3930, limit := 5631 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 4065, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_71_t_0_t_tail0 :
    instructionSequenceAt 3665 false { bytes := bytes, pos := 3881, limit := 5631 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4065, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_71_t_0_t_tail23 :
    instructionSequenceAt 3707 false { bytes := bytes, pos := 5063, limit := 5631 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 5198, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_71_t_0_t_tail0 :
    instructionSequenceAt 3730 false { bytes := bytes, pos := 5014, limit := 5631 } =
      .ok ((((((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5198, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_74_t_0_t_tail23 :
    instructionSequenceAt 3763 false { bytes := bytes, pos := 2208, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 2343, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_74_t_0_t_tail0 :
    instructionSequenceAt 3786 false { bytes := bytes, pos := 2159, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false)[74]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2343, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_71_t_tail0 :
    instructionSequenceAt 3667 false { bytes := bytes, pos := 3879, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[71]!).childBody false).drop 0, .end), { bytes := bytes, pos := 4066, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_94_t_0_t_75_t_tail14 :
    instructionSequenceAt 3649 true { bytes := bytes, pos := 4104, limit := 5631 } =
      .ok ((((((((((((raw.core.codes[2]!).body)[55]!).childBody false)[94]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 14, .end), { bytes := bytes, pos := 4233, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
