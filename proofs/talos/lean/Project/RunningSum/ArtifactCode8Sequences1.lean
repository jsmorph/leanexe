import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_t_tail0 :
    instructionSequenceAt 4328 true { bytes := bytes, pos := 11563, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 12149, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail174 :
    instructionSequenceAt 4154 false { bytes := bytes, pos := 13293, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 174, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail160 :
    instructionSequenceAt 4168 false { bytes := bytes, pos := 13152, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 160, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail146 :
    instructionSequenceAt 4182 false { bytes := bytes, pos := 13011, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 146, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail114 :
    instructionSequenceAt 4214 false { bytes := bytes, pos := 12835, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 114, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail68 :
    instructionSequenceAt 4260 false { bytes := bytes, pos := 12705, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 68, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail38 :
    instructionSequenceAt 4290 false { bytes := bytes, pos := 12430, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 38, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_tail34 :
    instructionSequenceAt 4294 false { bytes := bytes, pos := 12235, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true).drop 34, .end), { bytes := bytes, pos := 13428, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
