import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 48, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 49, limit := 55 }) := by cbv

#print axioms function0_decoded

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 49, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 50, limit := 55 }) := by cbv

#print axioms function1_decoded

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 50, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 51, limit := 55 }) := by cbv

#print axioms function2_decoded

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 51, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 52, limit := 55 }) := by cbv

#print axioms function3_decoded

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 52, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 53, limit := 55 }) := by cbv

#print axioms function4_decoded

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 53, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 54, limit := 55 }) := by cbv

#print axioms function5_decoded

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 54, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 55, limit := 55 }) := by cbv

#print axioms function6_decoded

theorem functionTypeIndices_tail7 :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 55, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 55, limit := 55 }) := by rfl

theorem functionTypeIndices_tail6 :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 54, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function6_decoded functionTypeIndices_tail7

theorem functionTypeIndices_tail5 :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 53, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function5_decoded functionTypeIndices_tail6

theorem functionTypeIndices_tail4 :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 52, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function4_decoded functionTypeIndices_tail5

theorem functionTypeIndices_tail3 :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 51, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function3_decoded functionTypeIndices_tail4

theorem functionTypeIndices_tail2 :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 50, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function2_decoded functionTypeIndices_tail3

theorem functionTypeIndices_tail1 :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 49, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function1_decoded functionTypeIndices_tail2

theorem functionTypeIndices_tail0 :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 48, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  exact vectorLoop_eq_cons function0_decoded functionTypeIndices_tail1

theorem functionTypeIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 47, limit := 55 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 55, limit := 55 }) := by
  refine vector_eq_of_parts (length := 7)
    (itemsStart := { bytes := artifactBytes, pos := 48, limit := 55 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 46, limit := 12733 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 55, limit := 12733 }) := by
  refine sized_eq_of_parts (size := 8)
    (payload := { bytes := artifactBytes, pos := 47, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 55, limit := 55 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.ExpArm.Artifact
