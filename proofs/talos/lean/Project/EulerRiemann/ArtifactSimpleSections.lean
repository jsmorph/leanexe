import Project.EulerRiemann.ArtifactSimpleItems

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 1024, limit := 21767 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 1134, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 109)
    (payload := { bytes := artifactBytes, pos := 1025, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 1134, limit := 1134 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 1135, limit := 21767 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 1139, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 3)
    (payload := { bytes := artifactBytes, pos := 1136, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 1139, limit := 1139 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector_decoded
  · rfl

#print axioms memories_section_decoded

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 1140, limit := 21767 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 1173, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 32)
    (payload := { bytes := artifactBytes, pos := 1141, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 1173, limit := 1173 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact globals_vector_decoded
  · rfl

#print axioms globals_section_decoded

end Project.EulerRiemann.Artifact
