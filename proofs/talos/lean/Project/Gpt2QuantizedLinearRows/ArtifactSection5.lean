import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem memory0_decoded :
    memoryType { bytes := artifactBytes, pos := 144, limit := 146 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 146, limit := 146 }) := by cbv

#print axioms memory0_decoded

theorem memories_tail1 :
    Internal.vectorLoop memoryType 0 { bytes := artifactBytes, pos := 146, limit := 146 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 146, limit := 146 }) := by rfl

theorem memories_tail0 :
    Internal.vectorLoop memoryType 1 { bytes := artifactBytes, pos := 144, limit := 146 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 146, limit := 146 }) := by
  exact vectorLoop_eq_cons memory0_decoded memories_tail1

theorem memories_vector_decoded :
    vector memoryType { bytes := artifactBytes, pos := 143, limit := 146 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 146, limit := 146 }) := by
  refine vector_eq_of_parts (length := 1)
    (itemsStart := { bytes := artifactBytes, pos := 144, limit := 146 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact memories_tail0

theorem memories_section_decoded :
    sized (vector memoryType) { bytes := artifactBytes, pos := 142, limit := 4741 } = .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 146, limit := 4741 }) := by
  refine sized_eq_of_parts (size := 3)
    (payload := { bytes := artifactBytes, pos := 143, limit := 4741 }) (finish := { bytes := artifactBytes, pos := 146, limit := 146 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact memories_vector_decoded
  · rfl

#print axioms memories_section_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
