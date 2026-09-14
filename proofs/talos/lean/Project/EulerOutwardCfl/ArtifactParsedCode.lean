import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardCfl.ArtifactParsedStates

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 2544 5 afterExports { bytes := artifactBytes, pos := 315, limit := 2557 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sectionLoop_eq_step (fuel := 2543) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 316, limit := 2557 }) (next := { bytes := artifactBytes, pos := 2557, limit := 2557 })
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

end Project.EulerOutwardCfl.Artifact
