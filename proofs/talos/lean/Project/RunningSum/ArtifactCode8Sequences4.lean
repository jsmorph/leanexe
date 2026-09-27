import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences3

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail73 :
    instructionSequenceAt 4344 false { bytes := bytes, pos := 13797, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 73, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail28 :
    instructionSequenceAt 4389 false { bytes := bytes, pos := 11418, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 28, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail0 :
    instructionSequenceAt 4417 false { bytes := bytes, pos := 11357, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_tail10 :
    instructionSequenceAt 4419 false { bytes := bytes, pos := 10739, limit := 14961 } =
      .ok ((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true).drop 10, .end), { bytes := bytes, pos := 14447, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_tail0 :
    instructionSequenceAt 4429 false { bytes := bytes, pos := 10711, limit := 14961 } =
      .ok ((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true).drop 0, .end), { bytes := bytes, pos := 14447, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail83 :
    instructionSequenceAt 4399 false { bytes := bytes, pos := 14662, limit := 14961 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 83, .end), { bytes := bytes, pos := 14791, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail65 :
    instructionSequenceAt 4417 false { bytes := bytes, pos := 14491, limit := 14961 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 65, .end), { bytes := bytes, pos := 14791, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail51 :
    instructionSequenceAt 4431 false { bytes := bytes, pos := 10613, limit := 14961 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 51, .end), { bytes := bytes, pos := 14791, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
