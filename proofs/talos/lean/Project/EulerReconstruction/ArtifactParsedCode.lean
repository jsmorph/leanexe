import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstruction.ArtifactParsedStates

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 5606 5 afterExports { bytes := artifactBytes, pos := 639, limit := 5619 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5619, limit := 5619 }) := by
  refine sectionLoop_eq_step (fuel := 5605) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 640, limit := 5619 }) (next := { bytes := artifactBytes, pos := 5619, limit := 5619 })
    (parsed := { afterExports with codes := Cache.raw.codes })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

#print axioms sections_from5

end Project.EulerReconstruction.Artifact
