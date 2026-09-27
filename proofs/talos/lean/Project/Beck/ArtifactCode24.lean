import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode24Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 8808, limit := 27068 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 9622, limit := 27068 }) := by
  refine code_eq_of_parts (size := 812)
    (payload := { bytes := artifactBytes, pos := 8810, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 8813, limit := 9622 })
    (bodyFinish := { bytes := artifactBytes, pos := 9622, limit := 9622 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_24_tail0
  · rfl

#print axioms code24_decoded

end Project.Beck.Artifact
