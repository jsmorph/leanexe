import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.EulerOutwardSpeed.ArtifactExportItems

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 4936 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 280, limit := 4936 }) := by
  cbv

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 281, limit := 4936 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 324, limit := 4936 }) := by
  cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 325, limit := 4936 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 329, limit := 4936 }) := by
  cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 330, limit := 4936 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 363, limit := 4936 }) := by
  cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 364, limit := 4936 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 484, limit := 4936 }) := by
  refine sized_eq_of_parts (size := 119)
    (payload := { bytes := artifactBytes, pos := 365, limit := 4936 })
    (finish := { bytes := artifactBytes, pos := 484, limit := 484 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded

end Project.EulerOutwardSpeed.Artifact
