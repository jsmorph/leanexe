import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode34Sequences3

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 21750, limit := 27068 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 23060, limit := 27068 }) := by
  refine code_eq_of_parts (size := 1308)
    (payload := { bytes := artifactBytes, pos := 21752, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 21755, limit := 23060 })
    (bodyFinish := { bytes := artifactBytes, pos := 23060, limit := 23060 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_34_tail0
  · rfl

#print axioms code34_decoded

end Project.Beck.Artifact
