import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode8Sequences5

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code8_decoded :
    code { bytes := bytes, pos := 10437, limit := 16553 } = .ok (raw.core.codes[8]!, { bytes := bytes, pos := 14961, limit := 16553 }) := by
  refine code_eq_of_parts (size := 4522)
    (payload := { bytes := bytes, pos := 10439, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 10443, limit := 14961 })
    (bodyFinish := { bytes := bytes, pos := 14961, limit := 14961 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.RunningSum.Artifact
