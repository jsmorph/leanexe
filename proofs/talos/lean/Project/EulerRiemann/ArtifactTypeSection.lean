import Project.EulerRiemann.ArtifactTypeItems

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 21767 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 1023, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 1012)
    (payload := { bytes := artifactBytes, pos := 11, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 1023, limit := 1023 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.EulerRiemann.Artifact
