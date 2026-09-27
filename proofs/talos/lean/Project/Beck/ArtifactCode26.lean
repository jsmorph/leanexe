import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode26Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 10915, limit := 27068 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 12826, limit := 27068 }) := by
  refine code_eq_of_parts (size := 1909)
    (payload := { bytes := artifactBytes, pos := 10917, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 10921, limit := 12826 })
    (bodyFinish := { bytes := artifactBytes, pos := 12826, limit := 12826 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_26_tail0
  · rfl

#print axioms code26_decoded

end Project.Beck.Artifact
