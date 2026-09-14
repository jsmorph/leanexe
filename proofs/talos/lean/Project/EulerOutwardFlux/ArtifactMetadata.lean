import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFlux.ArtifactTypeItems
import Project.EulerOutwardFlux.ArtifactExportItems

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 7175 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 456, limit := 7175 }) := by
  refine sized_eq_of_parts (size := 445)
    (payload := { bytes := artifactBytes, pos := 11, limit := 7175 }) (finish := { bytes := artifactBytes, pos := 456, limit := 456 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 457, limit := 7175 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 518, limit := 7175 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 519, limit := 7175 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 523, limit := 7175 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 524, limit := 7175 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 557, limit := 7175 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 558, limit := 7175 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 683, limit := 7175 }) := by
  refine sized_eq_of_parts (size := 124)
    (payload := { bytes := artifactBytes, pos := 559, limit := 7175 }) (finish := { bytes := artifactBytes, pos := 683, limit := 683 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerOutwardFlux.Artifact
