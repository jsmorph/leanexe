import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstruction.ArtifactTypeItems
import Project.EulerReconstruction.ArtifactExportItems

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 5619 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 430, limit := 5619 }) := by
  refine sized_eq_of_parts (size := 419)
    (payload := { bytes := artifactBytes, pos := 11, limit := 5619 }) (finish := { bytes := artifactBytes, pos := 430, limit := 430 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 431, limit := 5619 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 478, limit := 5619 }) := by cbv

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 479, limit := 5619 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 483, limit := 5619 }) := by cbv

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 484, limit := 5619 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 517, limit := 5619 }) := by cbv

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 518, limit := 5619 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 639, limit := 5619 }) := by
  refine sized_eq_of_parts (size := 120)
    (payload := { bytes := artifactBytes, pos := 519, limit := 5619 }) (finish := { bytes := artifactBytes, pos := 639, limit := 639 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded


end Project.EulerReconstruction.Artifact
