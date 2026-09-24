import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_50_t_0_t_tail18 :
    instructionSequenceAt 594 false { bytes := bytes, pos := 708, limit := 1161 } =
      .ok ((((((((raw.core.codes[1]!).body)[50]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 836, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_50_t_0_t_tail0 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 677, limit := 1161 } =
      .ok ((((((((raw.core.codes[1]!).body)[50]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 836, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_50_t_tail0 :
    instructionSequenceAt 614 false { bytes := bytes, pos := 675, limit := 1161 } =
      .ok ((((((raw.core.codes[1]!).body)[50]!).childBody false).drop 0, .end), { bytes := bytes, pos := 837, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_54_t_tail8 :
    instructionSequenceAt 602 true { bytes := bytes, pos := 857, limit := 1161 } =
      .ok ((((((raw.core.codes[1]!).body)[54]!).childBody false).drop 8, .end), { bytes := bytes, pos := 988, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_54_t_tail0 :
    instructionSequenceAt 610 true { bytes := bytes, pos := 844, limit := 1161 } =
      .ok ((((((raw.core.codes[1]!).body)[54]!).childBody false).drop 0, .end), { bytes := bytes, pos := 988, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_61_t_tail15 :
    instructionSequenceAt 588 false { bytes := bytes, pos := 1030, limit := 1161 } =
      .ok ((((((raw.core.codes[1]!).body)[61]!).childBody false).drop 15, .end), { bytes := bytes, pos := 1159, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_61_t_tail0 :
    instructionSequenceAt 603 false { bytes := bytes, pos := 1001, limit := 1161 } =
      .ok ((((((raw.core.codes[1]!).body)[61]!).childBody false).drop 0, .end), { bytes := bytes, pos := 1159, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail61 :
    instructionSequenceAt 605 false { bytes := bytes, pos := 999, limit := 1161 } =
      .ok ((((raw.core.codes[1]!).body).drop 61, .end), { bytes := bytes, pos := 1161, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail54 :
    instructionSequenceAt 612 false { bytes := bytes, pos := 842, limit := 1161 } =
      .ok ((((raw.core.codes[1]!).body).drop 54, .end), { bytes := bytes, pos := 1161, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail50 :
    instructionSequenceAt 616 false { bytes := bytes, pos := 673, limit := 1161 } =
      .ok ((((raw.core.codes[1]!).body).drop 50, .end), { bytes := bytes, pos := 1161, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail6 :
    instructionSequenceAt 660 false { bytes := bytes, pos := 529, limit := 1161 } =
      .ok ((((raw.core.codes[1]!).body).drop 6, .end), { bytes := bytes, pos := 1161, limit := 1161 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 666 false { bytes := bytes, pos := 495, limit := 1161 } =
      .ok ((((raw.core.codes[1]!).body).drop 0, .end), { bytes := bytes, pos := 1161, limit := 1161 }) := by
  cbv

theorem code1_decoded :
    code { bytes := bytes, pos := 490, limit := 2082 } = .ok (raw.core.codes[1]!, { bytes := bytes, pos := 1161, limit := 2082 }) := by
  refine code_eq_of_parts (size := 669)
    (payload := { bytes := bytes, pos := 492, limit := 2082 })
    (bodyStart := { bytes := bytes, pos := 495, limit := 1161 })
    (bodyFinish := { bytes := bytes, pos := 1161, limit := 1161 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.ByteIO.Artifact
