import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactParsedStates

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 5715 5 afterExports { bytes := artifactBytes, pos := 576, limit := 5728 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sectionLoop_eq_step (fuel := 5714) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 577, limit := 5728 }) (next := { bytes := artifactBytes, pos := 5728, limit := 5728 })
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

end Project.EulerOutwardGrid.Artifact
