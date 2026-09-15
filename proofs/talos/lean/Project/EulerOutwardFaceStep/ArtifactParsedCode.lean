import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFaceStep.ArtifactParsedStates

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 9064 5 afterExports { bytes := artifactBytes, pos := 897, limit := 9077 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sectionLoop_eq_step (fuel := 9063) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 898, limit := 9077 }) (next := { bytes := artifactBytes, pos := 9077, limit := 9077 })
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

end Project.EulerOutwardFaceStep.Artifact
