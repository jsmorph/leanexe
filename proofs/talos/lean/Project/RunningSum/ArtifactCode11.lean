import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 7 false { bytes := bytes, pos := 15892, limit := 15899 } =
      .ok ((((raw.core.codes[11]!).body).drop 0, .end), { bytes := bytes, pos := 15899, limit := 15899 }) := by
  cbv

theorem code11_decoded :
    code { bytes := bytes, pos := 15890, limit := 16553 } = .ok (raw.core.codes[11]!, { bytes := bytes, pos := 15899, limit := 16553 }) := by
  refine code_eq_of_parts (size := 8)
    (payload := { bytes := bytes, pos := 15891, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 15892, limit := 15899 })
    (bodyFinish := { bytes := bytes, pos := 15899, limit := 15899 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.RunningSum.Artifact
