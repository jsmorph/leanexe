import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences0

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_0_t_tail18 :
    instructionSequenceAt 3253 false { bytes := bytes, pos := 9638, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 9766, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_0_t_tail0 :
    instructionSequenceAt 3271 false { bytes := bytes, pos := 9607, limit := 10013 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9766, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_0_t_tail18 :
    instructionSequenceAt 3272 false { bytes := bytes, pos := 6794, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 6922, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_0_t_tail0 :
    instructionSequenceAt 3290 false { bytes := bytes, pos := 6763, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6922, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_93_t_0_t_tail18 :
    instructionSequenceAt 3203 false { bytes := bytes, pos := 7229, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 7357, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_93_t_0_t_tail0 :
    instructionSequenceAt 3221 false { bytes := bytes, pos := 7198, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7357, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_tail0 :
    instructionSequenceAt 3283 false { bytes := bytes, pos := 7689, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7851, limit := 10013 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_28_t_tail8 :
    instructionSequenceAt 3271 true { bytes := bytes, pos := 7871, limit := 10013 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := bytes, pos := 8002, limit := 10013 }) := by
  cbv


end Project.RunningSum.Artifact
