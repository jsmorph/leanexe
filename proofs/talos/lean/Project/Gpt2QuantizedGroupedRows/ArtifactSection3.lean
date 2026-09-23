import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 128, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 129, limit := 141 }) := by cbv

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 129, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 130, limit := 141 }) := by cbv

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 130, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 131, limit := 141 }) := by cbv

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 131, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 132, limit := 141 }) := by cbv

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 132, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 133, limit := 141 }) := by cbv

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 133, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 134, limit := 141 }) := by cbv

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 134, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 135, limit := 141 }) := by cbv

theorem function7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 135, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 136, limit := 141 }) := by cbv

theorem function8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 136, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 137, limit := 141 }) := by cbv

theorem function9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 137, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 138, limit := 141 }) := by cbv

theorem function10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 138, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 139, limit := 141 }) := by cbv

theorem function11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 139, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 140, limit := 141 }) := by cbv

theorem function12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 140, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 141, limit := 141 }) := by cbv

theorem functionTypeIndices_tail13 :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 141, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 141, limit := 141 }) := by rfl

theorem functionTypeIndices_tail12 :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 140, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function12_decoded functionTypeIndices_tail13

theorem functionTypeIndices_tail11 :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 139, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function11_decoded functionTypeIndices_tail12

theorem functionTypeIndices_tail10 :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 138, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function10_decoded functionTypeIndices_tail11

theorem functionTypeIndices_tail9 :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 137, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function9_decoded functionTypeIndices_tail10

theorem functionTypeIndices_tail8 :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 136, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function8_decoded functionTypeIndices_tail9

theorem functionTypeIndices_tail7 :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 135, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function7_decoded functionTypeIndices_tail8

theorem functionTypeIndices_tail6 :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 134, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function6_decoded functionTypeIndices_tail7

theorem functionTypeIndices_tail5 :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 133, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function5_decoded functionTypeIndices_tail6

theorem functionTypeIndices_tail4 :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 132, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function4_decoded functionTypeIndices_tail5

theorem functionTypeIndices_tail3 :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 131, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function3_decoded functionTypeIndices_tail4

theorem functionTypeIndices_tail2 :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 130, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function2_decoded functionTypeIndices_tail3

theorem functionTypeIndices_tail1 :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 129, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function1_decoded functionTypeIndices_tail2

theorem functionTypeIndices_tail0 :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 128, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  exact vectorLoop_eq_cons function0_decoded functionTypeIndices_tail1

theorem functionTypeIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 127, limit := 141 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 141, limit := 141 }) := by
  refine vector_eq_of_parts (length := 13)
    (itemsStart := { bytes := artifactBytes, pos := 128, limit := 141 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 126, limit := 5441 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 141, limit := 5441 }) := by
  refine sized_eq_of_parts (size := 14)
    (payload := { bytes := artifactBytes, pos := 127, limit := 5441 }) (finish := { bytes := artifactBytes, pos := 141, limit := 141 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
