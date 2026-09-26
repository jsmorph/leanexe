import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_38_e_24_t_0_t_30_e_tail7 :
    instructionSequenceAt 1133 false { bytes := bytes, pos := 1001, limit := 1719 } =
      .ok ((((((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false)[0]!).childBody false)[30]!).childBody true).drop 7, .end), { bytes := bytes, pos := 1135, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_24_t_0_t_30_e_tail0 :
    instructionSequenceAt 1140 false { bytes := bytes, pos := 984, limit := 1719 } =
      .ok ((((((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false)[0]!).childBody false)[30]!).childBody true).drop 0, .end), { bytes := bytes, pos := 1135, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_24_t_0_t_tail65 :
    instructionSequenceAt 1107 false { bytes := bytes, pos := 1262, limit := 1719 } =
      .ok ((((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 65, .end), { bytes := bytes, pos := 1460, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_24_t_0_t_tail30 :
    instructionSequenceAt 1142 false { bytes := bytes, pos := 953, limit := 1719 } =
      .ok ((((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 30, .end), { bytes := bytes, pos := 1460, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_24_t_0_t_tail0 :
    instructionSequenceAt 1172 false { bytes := bytes, pos := 865, limit := 1719 } =
      .ok ((((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 1460, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_24_t_tail0 :
    instructionSequenceAt 1174 false { bytes := bytes, pos := 863, limit := 1719 } =
      .ok ((((((((raw.core.codes[0]!).body)[38]!).childBody true)[24]!).childBody false).drop 0, .end), { bytes := bytes, pos := 1461, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_61_t_tail9 :
    instructionSequenceAt 1128 true { bytes := bytes, pos := 1556, limit := 1719 } =
      .ok ((((((((raw.core.codes[0]!).body)[38]!).childBody true)[61]!).childBody false).drop 9, .otherwise), { bytes := bytes, pos := 1690, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_61_t_tail0 :
    instructionSequenceAt 1137 true { bytes := bytes, pos := 1539, limit := 1719 } =
      .ok ((((((((raw.core.codes[0]!).body)[38]!).childBody true)[61]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 1690, limit := 1719 }) := by
  cbv


end Project.RunningSum.Artifact
