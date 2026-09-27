import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode25Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 9622, limit := 27068 } = .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 10915, limit := 27068 }) := by
  refine code_eq_of_parts (size := 1291)
    (payload := { bytes := artifactBytes, pos := 9624, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 9627, limit := 10915 })
    (bodyFinish := { bytes := artifactBytes, pos := 10915, limit := 10915 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_25_tail0
  · rfl

#print axioms code25_decoded

end Project.Beck.Artifact
