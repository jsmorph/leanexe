import Project.EulerRiemann.ArtifactExportItems

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 1174, limit := 21767 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 1289, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 114)
    (payload := { bytes := artifactBytes, pos := 1175, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 1289, limit := 1289 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded

end Project.EulerRiemann.Artifact
