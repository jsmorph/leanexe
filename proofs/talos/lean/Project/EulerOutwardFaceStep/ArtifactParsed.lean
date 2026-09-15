import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFaceStep.ArtifactParsedSections

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 9077 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 9077 }) (finish := { bytes := artifactBytes, pos := 9077, limit := 9077 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.EulerOutwardFaceStep.Artifact
