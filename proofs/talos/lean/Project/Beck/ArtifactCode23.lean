import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode23Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 8207, limit := 27068 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 8808, limit := 27068 }) := by
  refine code_eq_of_parts (size := 599)
    (payload := { bytes := artifactBytes, pos := 8209, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 8212, limit := 8808 })
    (bodyFinish := { bytes := artifactBytes, pos := 8808, limit := 8808 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_23_tail0
  · rfl

#print axioms code23_decoded

end Project.Beck.Artifact
