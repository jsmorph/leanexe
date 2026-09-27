import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem memory0_decoded :
    memoryType { bytes := artifactBytes, pos := 58, limit := 60 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 60, limit := 60 }) := by cbv

#print axioms memory0_decoded

theorem memories_tail1 :
    Internal.vectorLoop memoryType 0 { bytes := artifactBytes, pos := 60, limit := 60 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 60, limit := 60 }) := by rfl

theorem memories_tail0 :
    Internal.vectorLoop memoryType 1 { bytes := artifactBytes, pos := 58, limit := 60 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 60, limit := 60 }) := by
  exact vectorLoop_eq_cons memory0_decoded memories_tail1

theorem memories_vector_decoded :
    vector memoryType { bytes := artifactBytes, pos := 57, limit := 60 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 60, limit := 60 }) := by
  refine vector_eq_of_parts (length := 1)
    (itemsStart := { bytes := artifactBytes, pos := 58, limit := 60 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact memories_tail0

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 56, limit := 12733 } = .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 60, limit := 12733 }) := by
  refine sized_eq_of_parts (size := 3)
    (payload := { bytes := artifactBytes, pos := 57, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 60, limit := 60 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector_decoded
  · rfl

#print axioms memories_section_decoded

end Project.ExpArm.Artifact
