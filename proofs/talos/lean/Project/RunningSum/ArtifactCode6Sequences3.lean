import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences2

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_t_196_t_tail8 :
    instructionSequenceAt 3103 true { bytes := bytes, pos := 9239, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[196]!).childBody false).drop 8, .end), { bytes := bytes, pos := 9370, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_196_t_tail0 :
    instructionSequenceAt 3111 true { bytes := bytes, pos := 9226, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[196]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9370, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_tail0 :
    instructionSequenceAt 3273 false { bytes := bytes, pos := 9605, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9767, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_38_t_tail8 :
    instructionSequenceAt 3261 true { bytes := bytes, pos := 9787, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[38]!).childBody false).drop 8, .end), { bytes := bytes, pos := 9918, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_38_t_tail0 :
    instructionSequenceAt 3269 true { bytes := bytes, pos := 9774, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[38]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9918, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_tail0 :
    instructionSequenceAt 3292 false { bytes := bytes, pos := 6761, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6923, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_28_t_tail8 :
    instructionSequenceAt 3280 true { bytes := bytes, pos := 6943, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := bytes, pos := 7074, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_28_t_tail0 :
    instructionSequenceAt 3288 true { bytes := bytes, pos := 6930, limit := 10013 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7074, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
