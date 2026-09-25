import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences4

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_t_tail137 :
    instructionSequenceAt 3172 true { bytes := bytes, pos := 8563, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 137, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail92 :
    instructionSequenceAt 3217 true { bytes := bytes, pos := 8428, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 92, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail83 :
    instructionSequenceAt 3226 true { bytes := bytes, pos := 8267, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 83, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail79 :
    instructionSequenceAt 3230 true { bytes := bytes, pos := 8098, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 79, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail28 :
    instructionSequenceAt 3281 true { bytes := bytes, pos := 7856, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 28, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail24 :
    instructionSequenceAt 3285 true { bytes := bytes, pos := 7687, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 24, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail0 :
    instructionSequenceAt 3309 true { bytes := bytes, pos := 7641, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_tail38 :
    instructionSequenceAt 3271 false { bytes := bytes, pos := 9772, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 38, .end), { bytes := bytes, pos := 10005, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
