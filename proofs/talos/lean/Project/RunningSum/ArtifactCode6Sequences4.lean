import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences3

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_t_93_t_tail0 :
    instructionSequenceAt 3223 false { bytes := bytes, pos := 7196, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7358, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_97_t_tail8 :
    instructionSequenceAt 3211 true { bytes := bytes, pos := 7378, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[97]!).childBody false).drop 8, .end), { bytes := bytes, pos := 7509, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_97_t_tail0 :
    instructionSequenceAt 3219 true { bytes := bytes, pos := 7365, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[97]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7509, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail205 :
    instructionSequenceAt 3104 true { bytes := bytes, pos := 9385, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 205, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail196 :
    instructionSequenceAt 3113 true { bytes := bytes, pos := 9224, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 196, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail192 :
    instructionSequenceAt 3117 true { bytes := bytes, pos := 9055, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 192, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail150 :
    instructionSequenceAt 3159 true { bytes := bytes, pos := 8893, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 150, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail141 :
    instructionSequenceAt 3168 true { bytes := bytes, pos := 8732, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 141, .otherwise), { bytes := bytes, pos := 9535, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
