import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 364 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 18, limit := 364 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 18, limit := 364 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 24, limit := 364 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 24, limit := 364 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 29, limit := 364 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 29, limit := 364 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 38, limit := 364 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 38, limit := 364 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 43, limit := 364 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 43, limit := 364 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 48, limit := 364 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 48, limit := 364 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 53, limit := 364 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 53, limit := 364 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 61, limit := 364 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 61, limit := 364 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 66, limit := 364 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 66, limit := 364 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 71, limit := 364 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 71, limit := 364 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 76, limit := 364 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 76, limit := 364 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 82, limit := 364 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 82, limit := 364 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 87, limit := 364 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 364 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 95, limit := 364 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 95, limit := 364 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 101, limit := 364 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 101, limit := 364 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 107, limit := 364 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 107, limit := 364 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 113, limit := 364 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 113, limit := 364 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 121, limit := 364 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 121, limit := 364 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 127, limit := 364 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 127, limit := 364 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 133, limit := 364 }) := by cbv

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 133, limit := 364 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 141, limit := 364 }) := by cbv

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 141, limit := 364 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 149, limit := 364 }) := by cbv

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 149, limit := 364 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 157, limit := 364 }) := by cbv

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 157, limit := 364 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 162, limit := 364 }) := by cbv

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 162, limit := 364 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 167, limit := 364 }) := by cbv

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 167, limit := 364 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 173, limit := 364 }) := by cbv

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 173, limit := 364 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 180, limit := 364 }) := by cbv

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 180, limit := 364 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 188, limit := 364 }) := by cbv

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 188, limit := 364 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 196, limit := 364 }) := by cbv

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 196, limit := 364 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 204, limit := 364 }) := by cbv

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 204, limit := 364 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 212, limit := 364 }) := by cbv

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 212, limit := 364 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 220, limit := 364 }) := by cbv

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 220, limit := 364 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 229, limit := 364 }) := by cbv

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 229, limit := 364 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 238, limit := 364 }) := by cbv

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 238, limit := 364 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 247, limit := 364 }) := by cbv

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 247, limit := 364 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 254, limit := 364 }) := by cbv

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 254, limit := 364 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 263, limit := 364 }) := by cbv

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 263, limit := 364 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 272, limit := 364 }) := by cbv

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 272, limit := 364 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 280, limit := 364 }) := by cbv

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 280, limit := 364 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 288, limit := 364 }) := by cbv

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 288, limit := 364 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 296, limit := 364 }) := by cbv

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 296, limit := 364 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 304, limit := 364 }) := by cbv

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 304, limit := 364 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 313, limit := 364 }) := by cbv

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 313, limit := 364 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 327, limit := 364 }) := by cbv

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 327, limit := 364 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 341, limit := 364 }) := by cbv

theorem type45_decoded :
    funcType { bytes := artifactBytes, pos := 341, limit := 364 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 347, limit := 364 }) := by cbv

theorem type46_decoded :
    funcType { bytes := artifactBytes, pos := 347, limit := 364 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 352, limit := 364 }) := by cbv

theorem type47_decoded :
    funcType { bytes := artifactBytes, pos := 352, limit := 364 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 355, limit := 364 }) := by cbv

theorem type48_decoded :
    funcType { bytes := artifactBytes, pos := 355, limit := 364 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 360, limit := 364 }) := by cbv

theorem type49_decoded :
    funcType { bytes := artifactBytes, pos := 360, limit := 364 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 364, limit := 364 }) := by cbv

theorem types_tail50_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 364, limit := 364 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 364, limit := 364 }) := by rfl

theorem types_tail49_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 360, limit := 364 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50_decoded

theorem types_tail48_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 355, limit := 364 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49_decoded

theorem types_tail47_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 352, limit := 364 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48_decoded

theorem types_tail46_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 347, limit := 364 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47_decoded

theorem types_tail45_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 341, limit := 364 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46_decoded

theorem types_tail44_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 327, limit := 364 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 313, limit := 364 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 304, limit := 364 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 296, limit := 364 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 288, limit := 364 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 280, limit := 364 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 272, limit := 364 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 263, limit := 364 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 254, limit := 364 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37_decoded

theorem types_tail35_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 247, limit := 364 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 238, limit := 364 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 229, limit := 364 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 220, limit := 364 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 212, limit := 364 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 204, limit := 364 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 196, limit := 364 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 188, limit := 364 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 180, limit := 364 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 173, limit := 364 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 167, limit := 364 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 162, limit := 364 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 157, limit := 364 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 149, limit := 364 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 141, limit := 364 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 133, limit := 364 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21_decoded

theorem types_tail19_decoded :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 127, limit := 364 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 121, limit := 364 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 113, limit := 364 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 107, limit := 364 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 101, limit := 364 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 95, limit := 364 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 87, limit := 364 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 82, limit := 364 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 76, limit := 364 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 71, limit := 364 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 66, limit := 364 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 61, limit := 364 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 53, limit := 364 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 48, limit := 364 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 43, limit := 364 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 38, limit := 364 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 29, limit := 364 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 24, limit := 364 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 18, limit := 364 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 12, limit := 364 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 364 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  refine vector_eq_of_parts (length := 50)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 364 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded


end Project.EulerOutwardGrid.Artifact
