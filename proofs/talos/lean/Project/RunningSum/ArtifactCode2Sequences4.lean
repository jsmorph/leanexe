import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences3

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_55_e_29_t_0_t_tail0 :
    instructionSequenceAt 3805 false { bytes := bytes, pos := 4833, limit := 5631 } =
      .ok ((((((((((raw.core.codes[2]!).body)[55]!).childBody true)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 5560, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail110 :
    instructionSequenceAt 3754 false { bytes := bytes, pos := 2611, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 110, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail78 :
    instructionSequenceAt 3786 false { bytes := bytes, pos := 2350, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 78, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail74 :
    instructionSequenceAt 3790 false { bytes := bytes, pos := 2155, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail26 :
    instructionSequenceAt 3838 false { bytes := bytes, pos := 2026, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 26, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail15 :
    instructionSequenceAt 3849 false { bytes := bytes, pos := 1828, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_27_t_0_t_tail0 :
    instructionSequenceAt 3864 false { bytes := bytes, pos := 1800, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[27]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 2779, limit := 5631 }) := by
  cbv

@[cbv_eval] theorem sequence_2_55_t_36_t_tail0 :
    instructionSequenceAt 3800 false { bytes := bytes, pos := 2939, limit := 5631 } =
      .ok ((((((((raw.core.codes[2]!).body)[55]!).childBody false)[36]!).childBody false).drop 0, .end), { bytes := bytes, pos := 3110, limit := 5631 }) := by
  cbv


end Project.RunningSum.Artifact
