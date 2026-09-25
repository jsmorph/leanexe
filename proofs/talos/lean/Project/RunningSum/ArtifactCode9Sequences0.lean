import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_50_t_0_t_tail18 :
    instructionSequenceAt 594 false { bytes := bytes, pos := 15179, limit := 15632 } =
      .ok ((((((((raw.core.codes[9]!).body)[50]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 15307, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_50_t_0_t_tail0 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 15148, limit := 15632 } =
      .ok ((((((((raw.core.codes[9]!).body)[50]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15307, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_50_t_tail0 :
    instructionSequenceAt 614 false { bytes := bytes, pos := 15146, limit := 15632 } =
      .ok ((((((raw.core.codes[9]!).body)[50]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15308, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_54_t_tail8 :
    instructionSequenceAt 602 true { bytes := bytes, pos := 15328, limit := 15632 } =
      .ok ((((((raw.core.codes[9]!).body)[54]!).childBody false).drop 8, .end), { bytes := bytes, pos := 15459, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_54_t_tail0 :
    instructionSequenceAt 610 true { bytes := bytes, pos := 15315, limit := 15632 } =
      .ok ((((((raw.core.codes[9]!).body)[54]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15459, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_61_t_tail15 :
    instructionSequenceAt 588 false { bytes := bytes, pos := 15501, limit := 15632 } =
      .ok ((((((raw.core.codes[9]!).body)[61]!).childBody false).drop 15, .end), { bytes := bytes, pos := 15630, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_61_t_tail0 :
    instructionSequenceAt 603 false { bytes := bytes, pos := 15472, limit := 15632 } =
      .ok ((((((raw.core.codes[9]!).body)[61]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15630, limit := 15632 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail61 :
    instructionSequenceAt 605 false { bytes := bytes, pos := 15470, limit := 15632 } =
      .ok ((((raw.core.codes[9]!).body).drop 61, .end), { bytes := bytes, pos := 15632, limit := 15632 }) := by
  cbv


end Project.RunningSum.Artifact
