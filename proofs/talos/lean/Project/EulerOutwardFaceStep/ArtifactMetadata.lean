import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFaceStep.ArtifactTypeItems
import Project.EulerOutwardFaceStep.ArtifactExportItems

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 9077 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 649, limit := 9077 }) := by
  refine sized_eq_of_parts (size := 638)
    (payload := { bytes := artifactBytes, pos := 11, limit := 9077 }) (finish := { bytes := artifactBytes, pos := 649, limit := 649 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 650, limit := 9077 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 727, limit := 9077 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 728, limit := 9077 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 732, limit := 9077 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 733, limit := 9077 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 766, limit := 9077 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 767, limit := 9077 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 897, limit := 9077 }) := by
  refine sized_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 769, limit := 9077 }) (finish := { bytes := artifactBytes, pos := 897, limit := 897 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerOutwardFaceStep.Artifact
