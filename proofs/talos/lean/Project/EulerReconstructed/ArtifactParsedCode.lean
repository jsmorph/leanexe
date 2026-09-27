import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstructed.ArtifactParsedStates

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 30713 5 afterExports { bytes := artifactBytes, pos := 1966, limit := 30726 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  refine sectionLoop_eq_step (fuel := 30712) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 1967, limit := 30726 }) (next := { bytes := artifactBytes, pos := 30726, limit := 30726 })
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

end Project.EulerReconstructed.Artifact
