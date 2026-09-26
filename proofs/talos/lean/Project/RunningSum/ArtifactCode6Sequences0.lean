import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_0_t_tail18 :
    instructionSequenceAt 3263 false { bytes := bytes, pos := 7722, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 7850, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_0_t_tail0 :
    instructionSequenceAt 3281 false { bytes := bytes, pos := 7691, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7850, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_0_t_tail18 :
    instructionSequenceAt 3208 false { bytes := bytes, pos := 8133, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 8261, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_0_t_tail0 :
    instructionSequenceAt 3226 false { bytes := bytes, pos := 8102, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8261, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_0_t_tail18 :
    instructionSequenceAt 3150 false { bytes := bytes, pos := 8598, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 8726, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_0_t_tail0 :
    instructionSequenceAt 3168 false { bytes := bytes, pos := 8567, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8726, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_0_t_tail18 :
    instructionSequenceAt 3095 false { bytes := bytes, pos := 9090, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 9218, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_0_t_tail0 :
    instructionSequenceAt 3113 false { bytes := bytes, pos := 9059, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9218, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
