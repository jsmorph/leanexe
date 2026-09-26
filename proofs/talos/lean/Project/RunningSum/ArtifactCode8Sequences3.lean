import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences2

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_10_e_tail0 :
    instructionSequenceAt 4405 false { bytes := bytes, pos := 10867, limit := 14961 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 11356, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_tail0 :
    instructionSequenceAt 4387 false { bytes := bytes, pos := 11420, limit := 14961 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 13674, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_tail10 :
    instructionSequenceAt 4407 true { bytes := bytes, pos := 10769, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false).drop 10, .otherwise), { bytes := bytes, pos := 11357, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_tail0 :
    instructionSequenceAt 4417 true { bytes := bytes, pos := 10741, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 11357, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail143 :
    instructionSequenceAt 4274 false { bytes := bytes, pos := 14312, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 143, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail130 :
    instructionSequenceAt 4287 false { bytes := bytes, pos := 14184, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 130, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail117 :
    instructionSequenceAt 4300 false { bytes := bytes, pos := 14055, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 117, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_tail101 :
    instructionSequenceAt 4316 false { bytes := bytes, pos := 13927, limit := 14961 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true).drop 101, .end), { bytes := bytes, pos := 14446, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
