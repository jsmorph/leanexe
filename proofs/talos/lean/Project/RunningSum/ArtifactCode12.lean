import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail43 :
    instructionSequenceAt 305 false { bytes := bytes, pos := 16092, limit := 16252 } =
      .ok ((((raw.core.codes[12]!).body).drop 43, .end), { bytes := bytes, pos := 16252, limit := 16252 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail25 :
    instructionSequenceAt 323 false { bytes := bytes, pos := 15963, limit := 16252 } =
      .ok ((((raw.core.codes[12]!).body).drop 25, .end), { bytes := bytes, pos := 16252, limit := 16252 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 348 false { bytes := bytes, pos := 15904, limit := 16252 } =
      .ok ((((raw.core.codes[12]!).body).drop 0, .end), { bytes := bytes, pos := 16252, limit := 16252 }) := by
  cbv

theorem code12_decoded :
    code { bytes := bytes, pos := 15899, limit := 16553 } = .ok (raw.core.codes[12]!, { bytes := bytes, pos := 16252, limit := 16553 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := bytes, pos := 15901, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 15904, limit := 16252 })
    (bodyFinish := { bytes := bytes, pos := 16252, limit := 16252 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.RunningSum.Artifact
