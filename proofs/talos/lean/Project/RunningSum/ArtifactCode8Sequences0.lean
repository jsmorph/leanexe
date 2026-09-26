import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_34_t_0_t_tail23 :
    instructionSequenceAt 4267 false { bytes := bytes, pos := 12288, limit := 14961 } =
      .ok ((((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 12423, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_34_t_0_t_tail0 :
    instructionSequenceAt 4290 false { bytes := bytes, pos := 12239, limit := 14961 } =
      .ok ((((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12423, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_34_t_tail0 :
    instructionSequenceAt 4292 false { bytes := bytes, pos := 12237, limit := 14961 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true)[34]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12424, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_38_t_tail14 :
    instructionSequenceAt 4274 true { bytes := bytes, pos := 12462, limit := 14961 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true)[38]!).childBody false).drop 14, .end), { bytes := bytes, pos := 12591, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_e_38_t_tail0 :
    instructionSequenceAt 4288 true { bytes := bytes, pos := 12432, limit := 14961 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody true)[38]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12591, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_t_tail83 :
    instructionSequenceAt 4245 true { bytes := bytes, pos := 12020, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody false).drop 83, .otherwise), { bytes := bytes, pos := 12149, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_t_tail57 :
    instructionSequenceAt 4271 true { bytes := bytes, pos := 11875, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody false).drop 57, .otherwise), { bytes := bytes, pos := 12149, limit := 14961 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_51_e_10_e_28_t_0_t_55_t_tail43 :
    instructionSequenceAt 4285 true { bytes := bytes, pos := 11648, limit := 14961 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[51]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[55]!).childBody false).drop 43, .otherwise), { bytes := bytes, pos := 12149, limit := 14961 }) := by
  cbv


end Project.RunningSum.Artifact
