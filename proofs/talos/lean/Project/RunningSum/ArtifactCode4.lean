import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode4Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code4_decoded :
    code { bytes := bytes, pos := 5654, limit := 16553 } = .ok (raw.core.codes[4]!, { bytes := bytes, pos := 6373, limit := 16553 }) := by
  refine code_eq_of_parts (size := 717)
    (payload := { bytes := bytes, pos := 5656, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 5659, limit := 6373 })
    (bodyFinish := { bytes := bytes, pos := 6373, limit := 6373 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.RunningSum.Artifact
