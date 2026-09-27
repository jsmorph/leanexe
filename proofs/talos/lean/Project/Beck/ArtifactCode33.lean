import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode33Sequences4

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 19522, limit := 27068 } = .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 21750, limit := 27068 }) := by
  refine code_eq_of_parts (size := 2226)
    (payload := { bytes := artifactBytes, pos := 19524, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 19527, limit := 21750 })
    (bodyFinish := { bytes := artifactBytes, pos := 21750, limit := 21750 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_33_tail0
  · rfl

#print axioms code33_decoded

end Project.Beck.Artifact
