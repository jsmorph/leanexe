import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences10

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 14014, limit := 27068 } = .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 18733, limit := 27068 }) := by
  refine code_eq_of_parts (size := 4717)
    (payload := { bytes := artifactBytes, pos := 14016, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 14019, limit := 18733 })
    (bodyFinish := { bytes := artifactBytes, pos := 18733, limit := 18733 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_30_tail0
  · rfl

#print axioms code30_decoded

end Project.Beck.Artifact
