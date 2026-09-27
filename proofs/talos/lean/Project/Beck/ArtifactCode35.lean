import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences6

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 23060, limit := 27068 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 26239, limit := 27068 }) := by
  refine code_eq_of_parts (size := 3177)
    (payload := { bytes := artifactBytes, pos := 23062, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 23065, limit := 26239 })
    (bodyFinish := { bytes := artifactBytes, pos := 26239, limit := 26239 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_35_tail0
  · rfl

#print axioms code35_decoded

end Project.Beck.Artifact
