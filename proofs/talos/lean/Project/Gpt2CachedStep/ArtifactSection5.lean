import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem memory0_decoded :
    memoryType { bytes := artifactBytes, pos := 391, limit := 393 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 393, limit := 393 }) := by cbv

theorem memories_tail1 :
    Internal.vectorLoop memoryType 0 { bytes := artifactBytes, pos := 393, limit := 393 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 393, limit := 393 }) := by rfl

theorem memories_tail0 :
    Internal.vectorLoop memoryType 1 { bytes := artifactBytes, pos := 391, limit := 393 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 393, limit := 393 }) := by
  exact vectorLoop_eq_cons memory0_decoded memories_tail1

theorem memories_vector_decoded :
    vector memoryType { bytes := artifactBytes, pos := 390, limit := 393 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 393, limit := 393 }) := by
  refine vector_eq_of_parts (length := 1)
    (itemsStart := { bytes := artifactBytes, pos := 391, limit := 393 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact memories_tail0

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 389, limit := 19083 } = .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 393, limit := 19083 }) := by
  refine sized_eq_of_parts (size := 3)
    (payload := { bytes := artifactBytes, pos := 390, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 393, limit := 393 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector_decoded
  · rfl

#print axioms memories_section_decoded

end Project.Gpt2CachedStep.Artifact
