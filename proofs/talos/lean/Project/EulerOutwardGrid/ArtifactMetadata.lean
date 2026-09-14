import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactTypeItems
import Project.EulerOutwardGrid.ArtifactExportItems

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 5728 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 364, limit := 5728 }) := by
  refine sized_eq_of_parts (size := 353)
    (payload := { bytes := artifactBytes, pos := 11, limit := 5728 }) (finish := { bytes := artifactBytes, pos := 364, limit := 364 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 365, limit := 5728 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 417, limit := 5728 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 418, limit := 5728 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 422, limit := 5728 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 423, limit := 5728 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 456, limit := 5728 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 457, limit := 5728 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 576, limit := 5728 }) := by
  refine sized_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 458, limit := 5728 }) (finish := { bytes := artifactBytes, pos := 576, limit := 576 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerOutwardGrid.Artifact
