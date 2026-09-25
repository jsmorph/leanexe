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
    instructionSequenceAt 594 false { bytes := bytes, pos := 15095, limit := 15548 } =
      .ok ((((((((raw.core.codes[9]!).body)[50]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 15223, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_50_t_0_t_tail0 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 15064, limit := 15548 } =
      .ok ((((((((raw.core.codes[9]!).body)[50]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15223, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_50_t_tail0 :
    instructionSequenceAt 614 false { bytes := bytes, pos := 15062, limit := 15548 } =
      .ok ((((((raw.core.codes[9]!).body)[50]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15224, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_54_t_tail8 :
    instructionSequenceAt 602 true { bytes := bytes, pos := 15244, limit := 15548 } =
      .ok ((((((raw.core.codes[9]!).body)[54]!).childBody false).drop 8, .end), { bytes := bytes, pos := 15375, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_54_t_tail0 :
    instructionSequenceAt 610 true { bytes := bytes, pos := 15231, limit := 15548 } =
      .ok ((((((raw.core.codes[9]!).body)[54]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15375, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_61_t_tail15 :
    instructionSequenceAt 588 false { bytes := bytes, pos := 15417, limit := 15548 } =
      .ok ((((((raw.core.codes[9]!).body)[61]!).childBody false).drop 15, .end), { bytes := bytes, pos := 15546, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_61_t_tail0 :
    instructionSequenceAt 603 false { bytes := bytes, pos := 15388, limit := 15548 } =
      .ok ((((((raw.core.codes[9]!).body)[61]!).childBody false).drop 0, .end), { bytes := bytes, pos := 15546, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail61 :
    instructionSequenceAt 605 false { bytes := bytes, pos := 15386, limit := 15548 } =
      .ok ((((raw.core.codes[9]!).body).drop 61, .end), { bytes := bytes, pos := 15548, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail54 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 15229, limit := 15548 } =
      .ok ((((raw.core.codes[9]!).body).drop 54, .end), { bytes := bytes, pos := 15548, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail50 :
    instructionSequenceAt 616 false { bytes := bytes, pos := 15060, limit := 15548 } =
      .ok ((((raw.core.codes[9]!).body).drop 50, .end), { bytes := bytes, pos := 15548, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail6 :
    instructionSequenceAt 660 false { bytes := bytes, pos := 14916, limit := 15548 } =
      .ok ((((raw.core.codes[9]!).body).drop 6, .end), { bytes := bytes, pos := 15548, limit := 15548 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 666 false { bytes := bytes, pos := 14882, limit := 15548 } =
      .ok ((((raw.core.codes[9]!).body).drop 0, .end), { bytes := bytes, pos := 15548, limit := 15548 }) := by
  cbv

theorem code9_decoded :
    code { bytes := bytes, pos := 14877, limit := 16469 } = .ok (raw.core.codes[9]!, { bytes := bytes, pos := 15548, limit := 16469 }) := by
  refine code_eq_of_parts (size := 669)
    (payload := { bytes := bytes, pos := 14879, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 14882, limit := 15548 })
    (bodyFinish := { bytes := bytes, pos := 15548, limit := 15548 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.RunningSum.Artifact
