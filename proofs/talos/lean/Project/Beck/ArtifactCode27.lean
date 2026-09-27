import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode27Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 12826, limit := 27068 } = .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 13479, limit := 27068 }) := by
  refine code_eq_of_parts (size := 651)
    (payload := { bytes := artifactBytes, pos := 12828, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 12831, limit := 13479 })
    (bodyFinish := { bytes := artifactBytes, pos := 13479, limit := 13479 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_27_tail0
  · rfl

#print axioms code27_decoded

end Project.Beck.Artifact
