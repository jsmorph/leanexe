import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode9Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code9_decoded :
    code { bytes := bytes, pos := 14961, limit := 16553 } = .ok (raw.core.codes[9]!, { bytes := bytes, pos := 15632, limit := 16553 }) := by
  refine code_eq_of_parts (size := 669)
    (payload := { bytes := bytes, pos := 14963, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 14966, limit := 15632 })
    (bodyFinish := { bytes := bytes, pos := 15632, limit := 15632 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.RunningSum.Artifact
