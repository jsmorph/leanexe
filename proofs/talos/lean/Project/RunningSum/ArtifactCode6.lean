import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode6Sequences7

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code6_decoded :
    code { bytes := bytes, pos := 6678, limit := 16553 } = .ok (raw.core.codes[6]!, { bytes := bytes, pos := 10013, limit := 16553 }) := by
  refine code_eq_of_parts (size := 3333)
    (payload := { bytes := bytes, pos := 6680, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 6683, limit := 10013 })
    (bodyFinish := { bytes := bytes, pos := 10013, limit := 10013 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.RunningSum.Artifact
