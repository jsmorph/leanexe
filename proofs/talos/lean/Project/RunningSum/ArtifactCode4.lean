import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail127 :
    instructionSequenceAt 554 false { bytes := bytes, pos := 6638, limit := 6806 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 127, .end), { bytes := bytes, pos := 6766, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail85 :
    instructionSequenceAt 596 false { bytes := bytes, pos := 6500, limit := 6806 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := bytes, pos := 6766, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail62 :
    instructionSequenceAt 619 false { bytes := bytes, pos := 6366, limit := 6806 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 62, .end), { bytes := bytes, pos := 6766, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail24 :
    instructionSequenceAt 657 false { bytes := bytes, pos := 6238, limit := 6806 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 24, .end), { bytes := bytes, pos := 6766, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_0_t_tail0 :
    instructionSequenceAt 681 false { bytes := bytes, pos := 6179, limit := 6806 } =
      .ok ((((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6766, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_12_t_tail0 :
    instructionSequenceAt 683 false { bytes := bytes, pos := 6177, limit := 6806 } =
      .ok ((((((((raw.core.codes[4]!).body)[15]!).childBody true)[12]!).childBody false).drop 0, .end), { bytes := bytes, pos := 6767, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_tail12 :
    instructionSequenceAt 685 false { bytes := bytes, pos := 6175, limit := 6806 } =
      .ok ((((((raw.core.codes[4]!).body)[15]!).childBody true).drop 12, .end), { bytes := bytes, pos := 6803, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_15_e_tail0 :
    instructionSequenceAt 697 false { bytes := bytes, pos := 6151, limit := 6806 } =
      .ok ((((((raw.core.codes[4]!).body)[15]!).childBody true).drop 0, .end), { bytes := bytes, pos := 6803, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail15 :
    instructionSequenceAt 699 false { bytes := bytes, pos := 6133, limit := 6806 } =
      .ok ((((raw.core.codes[4]!).body).drop 15, .end), { bytes := bytes, pos := 6806, limit := 6806 }) := by
  cbv

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 714 false { bytes := bytes, pos := 6092, limit := 6806 } =
      .ok ((((raw.core.codes[4]!).body).drop 0, .end), { bytes := bytes, pos := 6806, limit := 6806 }) := by
  cbv

theorem code4_decoded :
    code { bytes := bytes, pos := 6087, limit := 16469 } = .ok (raw.core.codes[4]!, { bytes := bytes, pos := 6806, limit := 16469 }) := by
  refine code_eq_of_parts (size := 717)
    (payload := { bytes := bytes, pos := 6089, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 6092, limit := 6806 })
    (bodyFinish := { bytes := bytes, pos := 6806, limit := 6806 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.RunningSum.Artifact
