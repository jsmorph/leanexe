import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences5

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_e_tail34 :
    instructionSequenceAt 3275 false { bytes := bytes, pos := 9603, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 34, .end), { bytes := bytes, pos := 10005, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_tail0 :
    instructionSequenceAt 3309 false { bytes := bytes, pos := 9535, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10005, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail97 :
    instructionSequenceAt 3221 true { bytes := bytes, pos := 7363, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 97, .otherwise), { bytes := bytes, pos := 7622, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail93 :
    instructionSequenceAt 3225 true { bytes := bytes, pos := 7194, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 93, .otherwise), { bytes := bytes, pos := 7622, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail28 :
    instructionSequenceAt 3290 true { bytes := bytes, pos := 6928, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 28, .otherwise), { bytes := bytes, pos := 7622, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail24 :
    instructionSequenceAt 3294 true { bytes := bytes, pos := 6759, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 24, .otherwise), { bytes := bytes, pos := 7622, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail0 :
    instructionSequenceAt 3318 true { bytes := bytes, pos := 6713, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 7622, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_tail7 :
    instructionSequenceAt 3311 false { bytes := bytes, pos := 7639, limit := 10013 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody true).drop 7, .end), { bytes := bytes, pos := 10006, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
