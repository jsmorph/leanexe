import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 7 false { bytes := bytes, pos := 1723, limit := 1730 } =
      .ok ((((raw.core.codes[1]!).body).drop 0, .end), { bytes := bytes, pos := 1730, limit := 1730 }) := by
  cbv

theorem code1_decoded :
    code { bytes := bytes, pos := 1719, limit := 16553 } = .ok (raw.core.codes[1]!, { bytes := bytes, pos := 1730, limit := 16553 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := bytes, pos := 1720, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 1723, limit := 1730 })
    (bodyFinish := { bytes := bytes, pos := 1730, limit := 1730 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.RunningSum.Artifact
