import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem memories_item0 :
    memoryType { bytes := artifactBytes, pos := 904, limit := 906 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 906, limit := 906 }) := by cbv

theorem memories_tail1 :
    Internal.vectorLoop memoryType 0 { bytes := artifactBytes, pos := 906, limit := 906 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 906, limit := 906 }) := by rfl

theorem memories_tail0 :
    Internal.vectorLoop memoryType 1 { bytes := artifactBytes, pos := 904, limit := 906 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 906, limit := 906 }) := by
  exact vectorLoop_eq_cons memories_item0 memories_tail1

theorem memories_vector :
    vector memoryType { bytes := artifactBytes, pos := 903, limit := 906 } = .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 906, limit := 906 }) := by
  refine vector_eq_of_parts (length := 1) (itemsStart := { bytes := artifactBytes, pos := 904, limit := 906 }) ?_ ?_ memories_tail0
  · cbv
  · decide

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 902, limit := 16006 } = .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 906, limit := 16006 }) := by
  refine sized_eq_of_parts (size := 3) (payload := { bytes := artifactBytes, pos := 903, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 906, limit := 906 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector
  · rfl

#print axioms memories_section_decoded
end Project.TinyGpt2Hidden.Artifact
