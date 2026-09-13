import Project.EulerRiemann.ArtifactParsedSections

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := { bytes := artifactBytes, pos := 4, limit := 21767 })
    (sectionsStart := { bytes := artifactBytes, pos := 8, limit := 21767 }) (finish := { bytes := artifactBytes, pos := 21767, limit := 21767 }) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts

end Project.EulerRiemann.Artifact
