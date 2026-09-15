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

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 30726 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 1622, limit := 30726 }) := by
  refine sized_eq_of_parts (size := 1611)
    (payload := { bytes := artifactBytes, pos := 11, limit := 30726 }) (finish := { bytes := artifactBytes, pos := 1622, limit := 1622 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.EulerReconstructed.Artifact
