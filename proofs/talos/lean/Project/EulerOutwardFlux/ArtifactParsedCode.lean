import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFlux.ArtifactParsedStates

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 7162 5 afterExports { bytes := artifactBytes, pos := 683, limit := 7175 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine sectionLoop_eq_step (fuel := 7161) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 684, limit := 7175 }) (next := { bytes := artifactBytes, pos := 7175, limit := 7175 })
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

end Project.EulerOutwardFlux.Artifact
