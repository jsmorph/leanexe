import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences8

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 212, limit := 10666 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 9057, limit := 10666 }) := by
  refine code_eq_of_parts (size := 8843)
    (payload := { bytes := artifactBytes, pos := 214, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 217, limit := 9057 })
    (bodyFinish := { bytes := artifactBytes, pos := 9057, limit := 9057 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.ExpArm.Artifact
