import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode19Sequences3

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 6151, limit := 27068 } = .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 7717, limit := 27068 }) := by
  refine code_eq_of_parts (size := 1564)
    (payload := { bytes := artifactBytes, pos := 6153, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 6156, limit := 7717 })
    (bodyFinish := { bytes := artifactBytes, pos := 7717, limit := 7717 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_19_tail0
  · rfl

#print axioms code19_decoded

end Project.Beck.Artifact
