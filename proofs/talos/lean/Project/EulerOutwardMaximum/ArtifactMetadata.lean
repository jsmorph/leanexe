import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardMaximum.ArtifactTypeItems
import Project.EulerOutwardMaximum.ArtifactExportItems

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 5260 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 334, limit := 5260 }) := by
  refine sized_eq_of_parts (size := 323)
    (payload := { bytes := artifactBytes, pos := 11, limit := 5260 }) (finish := { bytes := artifactBytes, pos := 334, limit := 334 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 335, limit := 5260 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 384, limit := 5260 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 385, limit := 5260 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 389, limit := 5260 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 390, limit := 5260 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 423, limit := 5260 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 424, limit := 5260 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 548, limit := 5260 }) := by
  refine sized_eq_of_parts (size := 123)
    (payload := { bytes := artifactBytes, pos := 425, limit := 5260 }) (finish := { bytes := artifactBytes, pos := 548, limit := 548 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerOutwardMaximum.Artifact
