import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactMemorySectionItems

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem memories_tail1_decoded :
    Internal.vectorLoop memoryType 0 { bytes := artifactBytes, pos := 2843, limit := 2843 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 2843, limit := 2843 }) := by rfl

theorem memories_tail0_decoded :
    Internal.vectorLoop memoryType 1 { bytes := artifactBytes, pos := 2841, limit := 2843 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 2843, limit := 2843 }) := by
  exact vectorLoop_eq_cons memory0_decoded memories_tail1_decoded

theorem memories_vector_decoded :
    vector memoryType { bytes := artifactBytes, pos := 2840, limit := 2843 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 2843, limit := 2843 }) := by
  refine vector_eq_of_parts (length := 1)
    (itemsStart := { bytes := artifactBytes, pos := 2841, limit := 2843 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact memories_tail0_decoded

#print axioms memories_vector_decoded

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 2839, limit := 45644 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 2843, limit := 45644 }) := by
  refine sized_eq_of_parts (size := 3)
    (payload := { bytes := artifactBytes, pos := 2840, limit := 45644 }) (finish := { bytes := artifactBytes, pos := 2843, limit := 2843 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector_decoded
  · rfl

#print axioms memories_section_decoded

end Project.EulerCertificate.Artifact
