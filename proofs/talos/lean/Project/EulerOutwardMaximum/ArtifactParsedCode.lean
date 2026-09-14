import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardMaximum.ArtifactParsedStates

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 5247 5 afterExports { bytes := artifactBytes, pos := 548, limit := 5260 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 5260, limit := 5260 }) := by
  refine sectionLoop_eq_step (fuel := 5246) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 549, limit := 5260 }) (next := { bytes := artifactBytes, pos := 5260, limit := 5260 })
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

end Project.EulerOutwardMaximum.Artifact
