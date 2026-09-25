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

@[cbv_eval] theorem sequence_0_38_e_tail61 :
    instructionSequenceAt 1139 false { bytes := bytes, pos := 1537, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 61, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_tail24 :
    instructionSequenceAt 1176 false { bytes := bytes, pos := 861, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 24, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_38_e_tail0 :
    instructionSequenceAt 1200 false { bytes := bytes, pos := 813, limit := 1719 } =
      .ok ((((((raw.core.codes[0]!).body)[38]!).childBody true).drop 0, .end), { bytes := bytes, pos := 1708, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail38 :
    instructionSequenceAt 1202 false { bytes := bytes, pos := 790, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 38, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail16 :
    instructionSequenceAt 1224 false { bytes := bytes, pos := 619, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 16, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3 :
    instructionSequenceAt 1237 false { bytes := bytes, pos := 484, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 3, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 1240 false { bytes := bytes, pos := 479, limit := 1719 } =
      .ok ((((raw.core.codes[0]!).body).drop 0, .end), { bytes := bytes, pos := 1719, limit := 1719 }) := by
  cbv

theorem code0_decoded :
    code { bytes := bytes, pos := 474, limit := 16469 } = .ok (raw.core.codes[0]!, { bytes := bytes, pos := 1719, limit := 16469 }) := by
  refine code_eq_of_parts (size := 1243)
    (payload := { bytes := bytes, pos := 476, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 479, limit := 1719 })
    (bodyFinish := { bytes := bytes, pos := 1719, limit := 1719 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.RunningSum.Artifact
