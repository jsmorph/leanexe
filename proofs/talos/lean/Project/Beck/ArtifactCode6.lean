import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode6Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 3678, limit := 27068 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 5006, limit := 27068 }) := by
  refine code_eq_of_parts (size := 1326)
    (payload := { bytes := artifactBytes, pos := 3680, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 3683, limit := 5006 })
    (bodyFinish := { bytes := artifactBytes, pos := 5006, limit := 5006 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.Beck.Artifact
