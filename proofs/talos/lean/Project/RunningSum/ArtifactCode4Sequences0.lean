import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail127 :
    instructionSequenceAt 554 false { bytes := bytes, pos := 6205, limit := 6373 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 127, .end), { bytes := bytes, pos := 6333, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail85 :
    instructionSequenceAt 596 false { bytes := bytes, pos := 6067, limit := 6373 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := bytes, pos := 6333, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail62 :
    instructionSequenceAt 619 false { bytes := bytes, pos := 5933, limit := 6373 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 62, .end), { bytes := bytes, pos := 6333, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail24 :
    instructionSequenceAt 657 false { bytes := bytes, pos := 5805, limit := 6373 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 24, .end), { bytes := bytes, pos := 6333, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail0 :
    instructionSequenceAt 681 false { bytes := bytes, pos := 5746, limit := 6373 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6333, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_tail0 :
    instructionSequenceAt 683 false { bytes := bytes, pos := 5744, limit := 6373 } =
      .ok ((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6334, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_tail12 :
    instructionSequenceAt 685 false { bytes := bytes, pos := 5742, limit := 6373 } =
      .ok ((((((raw.core.codes[4]!).body)[15]!).childBody true).drop 12, .end), { bytes := bytes, pos := 6370, limit := 6373 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_tail0 :
    instructionSequenceAt 697 false { bytes := bytes, pos := 5718, limit := 6373 } =
      .ok ((((((raw.core.codes[4]!).body)[15]!).childBody true).drop 0, .end), { bytes := bytes, pos := 6370, limit := 6373 }) := by
  cbv


end Project.RunningSum.Artifact
