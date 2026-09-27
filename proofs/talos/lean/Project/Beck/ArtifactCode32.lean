import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode32Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 18783, limit := 27068 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 19522, limit := 27068 }) := by
  refine code_eq_of_parts (size := 737)
    (payload := { bytes := artifactBytes, pos := 18785, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 18788, limit := 19522 })
    (bodyFinish := { bytes := artifactBytes, pos := 19522, limit := 19522 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_32_tail0
  · rfl

#print axioms code32_decoded

end Project.Beck.Artifact
