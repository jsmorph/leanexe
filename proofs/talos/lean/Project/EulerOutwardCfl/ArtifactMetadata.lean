import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardCfl.ArtifactTypeItems
import Project.EulerOutwardCfl.ArtifactExportItems

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 2557 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 126, limit := 2557 }) := by
  refine sized_eq_of_parts (size := 116)
    (payload := { bytes := artifactBytes, pos := 10, limit := 2557 }) (finish := { bytes := artifactBytes, pos := 126, limit := 126 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 127, limit := 2557 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 149, limit := 2557 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 150, limit := 2557 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 154, limit := 2557 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 155, limit := 2557 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 188, limit := 2557 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 189, limit := 2557 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 315, limit := 2557 }) := by
  refine sized_eq_of_parts (size := 125)
    (payload := { bytes := artifactBytes, pos := 190, limit := 2557 }) (finish := { bytes := artifactBytes, pos := 315, limit := 315 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerOutwardCfl.Artifact
