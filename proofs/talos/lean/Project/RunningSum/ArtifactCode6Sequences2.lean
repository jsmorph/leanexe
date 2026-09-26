import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_t_28_t_tail0 :
    instructionSequenceAt 3279 true { bytes := bytes, pos := 7858, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8002, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_tail0 :
    instructionSequenceAt 3228 false { bytes := bytes, pos := 8100, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8262, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_83_t_tail8 :
    instructionSequenceAt 3216 true { bytes := bytes, pos := 8282, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[83]!).childBody false).drop 8, .end), { bytes := bytes, pos := 8413, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_83_t_tail0 :
    instructionSequenceAt 3224 true { bytes := bytes, pos := 8269, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[83]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8413, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_tail0 :
    instructionSequenceAt 3170 false { bytes := bytes, pos := 8565, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8727, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_141_t_tail8 :
    instructionSequenceAt 3158 true { bytes := bytes, pos := 8747, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[141]!).childBody false).drop 8, .end), { bytes := bytes, pos := 8878, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_141_t_tail0 :
    instructionSequenceAt 3166 true { bytes := bytes, pos := 8734, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[141]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8878, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_tail0 :
    instructionSequenceAt 3115 false { bytes := bytes, pos := 9057, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9219, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
