import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode0Sequences1

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code0_decoded :
    code { bytes := bytes, pos := 474, limit := 16553 } = .ok (raw.core.codes[0]!, { bytes := bytes, pos := 1719, limit := 16553 }) := by
  refine code_eq_of_parts (size := 1243)
    (payload := { bytes := bytes, pos := 476, limit := 16553 })
    (bodyStart := { bytes := bytes, pos := 479, limit := 1719 })
    (bodyFinish := { bytes := bytes, pos := 1719, limit := 1719 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.RunningSum.Artifact
