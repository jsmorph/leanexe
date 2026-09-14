import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 11, limit := 126 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 16, limit := 126 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 16, limit := 126 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 21, limit := 126 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 21, limit := 126 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 26, limit := 126 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 26, limit := 126 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 31, limit := 126 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 31, limit := 126 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 37, limit := 126 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 37, limit := 126 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 42, limit := 126 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 42, limit := 126 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 49, limit := 126 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 49, limit := 126 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 57, limit := 126 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 57, limit := 126 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 62, limit := 126 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 62, limit := 126 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 68, limit := 126 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 68, limit := 126 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 74, limit := 126 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 74, limit := 126 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 79, limit := 126 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 79, limit := 126 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 87, limit := 126 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 126 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 93, limit := 126 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 93, limit := 126 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 101, limit := 126 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 101, limit := 126 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 109, limit := 126 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 109, limit := 126 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 114, limit := 126 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 114, limit := 126 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 117, limit := 126 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 117, limit := 126 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 122, limit := 126 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 122, limit := 126 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 126, limit := 126 }) := by cbv

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 126, limit := 126 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 126, limit := 126 }) := by rfl

theorem types_tail19_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 122, limit := 126 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 117, limit := 126 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 114, limit := 126 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 109, limit := 126 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 101, limit := 126 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 93, limit := 126 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 87, limit := 126 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 79, limit := 126 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 74, limit := 126 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 68, limit := 126 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 62, limit := 126 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 57, limit := 126 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 49, limit := 126 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 42, limit := 126 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 37, limit := 126 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 31, limit := 126 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 26, limit := 126 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 21, limit := 126 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 16, limit := 126 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 11, limit := 126 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 10, limit := 126 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 126, limit := 126 }) := by
  refine vector_eq_of_parts (length := 20)
    (itemsStart := { bytes := artifactBytes, pos := 11, limit := 126 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded


end Project.EulerOutwardCfl.Artifact
