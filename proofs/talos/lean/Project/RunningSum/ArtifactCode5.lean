import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_10_e_tail27 :
    instructionSequenceAt 261 false { bytes := bytes, pos := 6532, limit := 6678 } =
      .ok ((((((raw.core.codes[5]!).body)[10]!).childBody true).drop 27, .end), { bytes := bytes, pos := 6669, limit := 6678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_10_e_tail0 :
    instructionSequenceAt 288 false { bytes := bytes, pos := 6475, limit := 6678 } =
      .ok ((((((raw.core.codes[5]!).body)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 6669, limit := 6678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail10 :
    instructionSequenceAt 290 false { bytes := bytes, pos := 6406, limit := 6678 } =
      .ok ((((raw.core.codes[5]!).body).drop 10, .end), { bytes := bytes, pos := 6678, limit := 6678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 300 false { bytes := bytes, pos := 6378, limit := 6678 } =
      .ok ((((raw.core.codes[5]!).body).drop 0, .end), { bytes := bytes, pos := 6678, limit := 6678 }) := by
  cbv

theorem code5_decoded :
    code { bytes := bytes, pos := 6373, limit := 16553 } = .ok (raw.core.codes[5]!, { bytes := bytes, pos := 6678, limit := 16553 }) := by
  refine code_eq_of_parts (size := 303)
    (payload := { bytes := bytes, pos := 6375, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 6378, limit := 6678 })
    (bodyFinish := { bytes := bytes, pos := 6678, limit := 6678 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.RunningSum.Artifact
