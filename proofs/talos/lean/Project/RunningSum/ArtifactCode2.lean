import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode2Sequences7

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code2_decoded :
    code { bytes := bytes, pos := 1730, limit := 16553 } = .ok (raw.core.codes[2]!, { bytes := bytes, pos := 5631, limit := 16553 }) := by
  refine code_eq_of_parts (size := 3899)
    (payload := { bytes := bytes, pos := 1732, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 1736, limit := 5631 })
    (bodyFinish := { bytes := bytes, pos := 5631, limit := 5631 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.RunningSum.Artifact
