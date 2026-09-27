import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstructed.ArtifactTypeItems
import Project.EulerReconstructed.ArtifactExportItems

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 1845, limit := 30726 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 1966, limit := 30726 }) := by
  refine sized_eq_of_parts (size := 120)
    (payload := { bytes := artifactBytes, pos := 1846, limit := 30726 }) (finish := { bytes := artifactBytes, pos := 1966, limit := 1966 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded

end Project.EulerReconstructed.Artifact
