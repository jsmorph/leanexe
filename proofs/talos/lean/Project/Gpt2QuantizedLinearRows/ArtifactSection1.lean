import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 11, limit := 125 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 19, limit := 125 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 19, limit := 125 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 28, limit := 125 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 28, limit := 125 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 34, limit := 125 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 34, limit := 125 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 48, limit := 125 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 48, limit := 125 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 61, limit := 125 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 61, limit := 125 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 73, limit := 125 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 73, limit := 125 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 80, limit := 125 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 80, limit := 125 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 92, limit := 125 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 92, limit := 125 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 108, limit := 125 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 108, limit := 125 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 113, limit := 125 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 113, limit := 125 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 116, limit := 125 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 116, limit := 125 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 121, limit := 125 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 121, limit := 125 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 125, limit := 125 }) := by cbv

theorem types_tail13 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 125, limit := 125 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 125, limit := 125 }) := by rfl

theorem types_tail12 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 121, limit := 125 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 116, limit := 125 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 113, limit := 125 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 108, limit := 125 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 92, limit := 125 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 80, limit := 125 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 73, limit := 125 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 61, limit := 125 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 48, limit := 125 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 34, limit := 125 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 28, limit := 125 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 19, limit := 125 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 11, limit := 125 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 10, limit := 125 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 125, limit := 125 }) := by
  refine vector_eq_of_parts (length := 13)
    (itemsStart := { bytes := artifactBytes, pos := 11, limit := 125 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 4757 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 125, limit := 4757 }) := by
  refine sized_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 10, limit := 4757 }) (finish := { bytes := artifactBytes, pos := 125, limit := 125 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
