import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 430 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 17, limit := 430 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 17, limit := 430 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 22, limit := 430 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 22, limit := 430 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 27, limit := 430 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 27, limit := 430 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 35, limit := 430 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 35, limit := 430 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 40, limit := 430 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 40, limit := 430 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 45, limit := 430 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 45, limit := 430 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 50, limit := 430 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 50, limit := 430 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 56, limit := 430 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 56, limit := 430 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 61, limit := 430 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 61, limit := 430 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 69, limit := 430 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 69, limit := 430 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 75, limit := 430 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 75, limit := 430 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 81, limit := 430 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 81, limit := 430 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 87, limit := 430 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 430 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 95, limit := 430 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 95, limit := 430 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 101, limit := 430 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 101, limit := 430 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 107, limit := 430 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 107, limit := 430 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 115, limit := 430 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 115, limit := 430 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 123, limit := 430 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 123, limit := 430 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 131, limit := 430 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 131, limit := 430 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 139, limit := 430 }) := by cbv

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 139, limit := 430 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 147, limit := 430 }) := by cbv

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 147, limit := 430 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 155, limit := 430 }) := by cbv

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 155, limit := 430 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 163, limit := 430 }) := by cbv

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 163, limit := 430 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 171, limit := 430 }) := by cbv

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 171, limit := 430 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 186, limit := 430 }) := by cbv

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 186, limit := 430 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 194, limit := 430 }) := by cbv

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 194, limit := 430 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 200, limit := 430 }) := by cbv

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 200, limit := 430 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 215, limit := 430 }) := by cbv

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 215, limit := 430 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 222, limit := 430 }) := by cbv

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 222, limit := 430 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 230, limit := 430 }) := by cbv

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 230, limit := 430 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 250, limit := 430 }) := by cbv

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 250, limit := 430 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 259, limit := 430 }) := by cbv

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 259, limit := 430 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 276, limit := 430 }) := by cbv

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 276, limit := 430 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 288, limit := 430 }) := by cbv

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 288, limit := 430 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 303, limit := 430 }) := by cbv

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 303, limit := 430 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 316, limit := 430 }) := by cbv

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 316, limit := 430 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 338, limit := 430 }) := by cbv

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 338, limit := 430 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 352, limit := 430 }) := by cbv

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 352, limit := 430 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 375, limit := 430 }) := by cbv

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 375, limit := 430 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 387, limit := 430 }) := by cbv

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 387, limit := 430 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 413, limit := 430 }) := by cbv

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 413, limit := 430 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 418, limit := 430 }) := by cbv

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 418, limit := 430 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 421, limit := 430 }) := by cbv

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 421, limit := 430 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 426, limit := 430 }) := by cbv

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 426, limit := 430 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 430, limit := 430 }) := by cbv

theorem types_tail45_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 430, limit := 430 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 430, limit := 430 }) := by rfl

theorem types_tail44_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 426, limit := 430 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 421, limit := 430 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 418, limit := 430 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 413, limit := 430 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 387, limit := 430 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 375, limit := 430 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 352, limit := 430 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 338, limit := 430 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 316, limit := 430 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37_decoded

theorem types_tail35_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 303, limit := 430 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 288, limit := 430 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 276, limit := 430 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 259, limit := 430 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 250, limit := 430 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 230, limit := 430 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 222, limit := 430 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 215, limit := 430 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 200, limit := 430 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 194, limit := 430 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 186, limit := 430 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 171, limit := 430 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 163, limit := 430 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 155, limit := 430 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 147, limit := 430 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 139, limit := 430 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21_decoded

theorem types_tail19_decoded :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 131, limit := 430 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 123, limit := 430 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 115, limit := 430 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 107, limit := 430 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 101, limit := 430 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 95, limit := 430 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 87, limit := 430 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 81, limit := 430 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 75, limit := 430 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 69, limit := 430 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 61, limit := 430 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 56, limit := 430 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 50, limit := 430 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 45, limit := 430 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 40, limit := 430 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 35, limit := 430 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 27, limit := 430 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 22, limit := 430 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 17, limit := 430 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 12, limit := 430 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 430 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 430, limit := 430 }) := by
  refine vector_eq_of_parts (length := 45)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 430 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded


end Project.EulerReconstruction.Artifact
