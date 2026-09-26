import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail0 :
    instructionSequenceAt 4328 false { bytes := bytes, pos := 12149, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 0, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_tail105 :
    instructionSequenceAt 4280 false { bytes := bytes, pos := 13545, limit := 14961 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 105, .end), { bytes := bytes, pos := 13673, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_tail55 :
    instructionSequenceAt 4330 false { bytes := bytes, pos := 11561, limit := 14961 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 55, .end), { bytes := bytes, pos := 13673, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_tail4 :
    instructionSequenceAt 4381 false { bytes := bytes, pos := 11431, limit := 14961 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 4, .end), { bytes := bytes, pos := 13673, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_tail0 :
    instructionSequenceAt 4385 false { bytes := bytes, pos := 11422, limit := 14961 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 13673, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_10_e_tail79 :
    instructionSequenceAt 4326 false { bytes := bytes, pos := 11219, limit := 14961 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 79, .end), { bytes := bytes, pos := 11356, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_10_e_tail63 :
    instructionSequenceAt 4342 false { bytes := bytes, pos := 11088, limit := 14961 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 63, .end), { bytes := bytes, pos := 11356, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_t_10_e_tail41 :
    instructionSequenceAt 4364 false { bytes := bytes, pos := 10960, limit := 14961 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 41, .end), { bytes := bytes, pos := 11356, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
