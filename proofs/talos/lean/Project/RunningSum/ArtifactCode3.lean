import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 19 false { bytes := bytes, pos := 5635, limit := 5654 } =
      .ok ((((raw.core.codes[3]!).body).drop 0, .end), { bytes := bytes, pos := 5654, limit := 5654 }) := by
  cbv

theorem code3_decoded :
    code { bytes := bytes, pos := 5631, limit := 16553 } = .ok (raw.core.codes[3]!, { bytes := bytes, pos := 5654, limit := 16553 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := bytes, pos := 5632, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 5635, limit := 5654 })
    (bodyFinish := { bytes := bytes, pos := 5654, limit := 5654 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.RunningSum.Artifact
