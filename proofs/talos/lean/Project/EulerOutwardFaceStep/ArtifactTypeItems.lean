import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 649 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 17, limit := 649 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 17, limit := 649 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 22, limit := 649 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 22, limit := 649 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 27, limit := 649 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 27, limit := 649 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 35, limit := 649 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 35, limit := 649 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 40, limit := 649 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 40, limit := 649 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 45, limit := 649 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 45, limit := 649 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 50, limit := 649 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 50, limit := 649 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 56, limit := 649 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 56, limit := 649 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 61, limit := 649 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 61, limit := 649 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 69, limit := 649 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 69, limit := 649 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 75, limit := 649 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 75, limit := 649 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 81, limit := 649 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 81, limit := 649 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 87, limit := 649 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 649 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 95, limit := 649 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 95, limit := 649 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 101, limit := 649 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 101, limit := 649 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 107, limit := 649 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 107, limit := 649 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 115, limit := 649 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 115, limit := 649 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 123, limit := 649 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 123, limit := 649 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 131, limit := 649 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 131, limit := 649 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 136, limit := 649 }) := by cbv

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 136, limit := 649 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 141, limit := 649 }) := by cbv

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 141, limit := 649 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 147, limit := 649 }) := by cbv

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 147, limit := 649 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 152, limit := 649 }) := by cbv

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 152, limit := 649 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 159, limit := 649 }) := by cbv

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 159, limit := 649 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 167, limit := 649 }) := by cbv

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 167, limit := 649 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 175, limit := 649 }) := by cbv

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 175, limit := 649 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 181, limit := 649 }) := by cbv

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 181, limit := 649 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 189, limit := 649 }) := by cbv

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 189, limit := 649 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 195, limit := 649 }) := by cbv

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 195, limit := 649 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 203, limit := 649 }) := by cbv

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 203, limit := 649 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 211, limit := 649 }) := by cbv

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 211, limit := 649 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 220, limit := 649 }) := by cbv

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 220, limit := 649 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 229, limit := 649 }) := by cbv

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 229, limit := 649 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 238, limit := 649 }) := by cbv

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 238, limit := 649 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 245, limit := 649 }) := by cbv

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 245, limit := 649 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 254, limit := 649 }) := by cbv

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 254, limit := 649 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 263, limit := 649 }) := by cbv

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 263, limit := 649 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 274, limit := 649 }) := by cbv

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 274, limit := 649 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 289, limit := 649 }) := by cbv

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 289, limit := 649 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 301, limit := 649 }) := by cbv

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 301, limit := 649 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 313, limit := 649 }) := by cbv

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 313, limit := 649 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 318, limit := 649 }) := by cbv

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 318, limit := 649 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 323, limit := 649 }) := by cbv

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 323, limit := 649 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 328, limit := 649 }) := by cbv

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 328, limit := 649 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 333, limit := 649 }) := by cbv

theorem type45_decoded :
    funcType { bytes := artifactBytes, pos := 333, limit := 649 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 343, limit := 649 }) := by cbv

theorem type46_decoded :
    funcType { bytes := artifactBytes, pos := 343, limit := 649 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 353, limit := 649 }) := by cbv

theorem type47_decoded :
    funcType { bytes := artifactBytes, pos := 353, limit := 649 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 365, limit := 649 }) := by cbv

theorem type48_decoded :
    funcType { bytes := artifactBytes, pos := 365, limit := 649 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 377, limit := 649 }) := by cbv

theorem type49_decoded :
    funcType { bytes := artifactBytes, pos := 377, limit := 649 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 389, limit := 649 }) := by cbv

theorem type50_decoded :
    funcType { bytes := artifactBytes, pos := 389, limit := 649 } =
      .ok (Cache.raw.types[50]!, { bytes := artifactBytes, pos := 401, limit := 649 }) := by cbv

theorem type51_decoded :
    funcType { bytes := artifactBytes, pos := 401, limit := 649 } =
      .ok (Cache.raw.types[51]!, { bytes := artifactBytes, pos := 407, limit := 649 }) := by cbv

theorem type52_decoded :
    funcType { bytes := artifactBytes, pos := 407, limit := 649 } =
      .ok (Cache.raw.types[52]!, { bytes := artifactBytes, pos := 413, limit := 649 }) := by cbv

theorem type53_decoded :
    funcType { bytes := artifactBytes, pos := 413, limit := 649 } =
      .ok (Cache.raw.types[53]!, { bytes := artifactBytes, pos := 422, limit := 649 }) := by cbv

theorem type54_decoded :
    funcType { bytes := artifactBytes, pos := 422, limit := 649 } =
      .ok (Cache.raw.types[54]!, { bytes := artifactBytes, pos := 439, limit := 649 }) := by cbv

theorem type55_decoded :
    funcType { bytes := artifactBytes, pos := 439, limit := 649 } =
      .ok (Cache.raw.types[55]!, { bytes := artifactBytes, pos := 447, limit := 649 }) := by cbv

theorem type56_decoded :
    funcType { bytes := artifactBytes, pos := 447, limit := 649 } =
      .ok (Cache.raw.types[56]!, { bytes := artifactBytes, pos := 455, limit := 649 }) := by cbv

theorem type57_decoded :
    funcType { bytes := artifactBytes, pos := 455, limit := 649 } =
      .ok (Cache.raw.types[57]!, { bytes := artifactBytes, pos := 463, limit := 649 }) := by cbv

theorem type58_decoded :
    funcType { bytes := artifactBytes, pos := 463, limit := 649 } =
      .ok (Cache.raw.types[58]!, { bytes := artifactBytes, pos := 471, limit := 649 }) := by cbv

theorem type59_decoded :
    funcType { bytes := artifactBytes, pos := 471, limit := 649 } =
      .ok (Cache.raw.types[59]!, { bytes := artifactBytes, pos := 481, limit := 649 }) := by cbv

theorem type60_decoded :
    funcType { bytes := artifactBytes, pos := 481, limit := 649 } =
      .ok (Cache.raw.types[60]!, { bytes := artifactBytes, pos := 491, limit := 649 }) := by cbv

theorem type61_decoded :
    funcType { bytes := artifactBytes, pos := 491, limit := 649 } =
      .ok (Cache.raw.types[61]!, { bytes := artifactBytes, pos := 500, limit := 649 }) := by cbv

theorem type62_decoded :
    funcType { bytes := artifactBytes, pos := 500, limit := 649 } =
      .ok (Cache.raw.types[62]!, { bytes := artifactBytes, pos := 509, limit := 649 }) := by cbv

theorem type63_decoded :
    funcType { bytes := artifactBytes, pos := 509, limit := 649 } =
      .ok (Cache.raw.types[63]!, { bytes := artifactBytes, pos := 519, limit := 649 }) := by cbv

theorem type64_decoded :
    funcType { bytes := artifactBytes, pos := 519, limit := 649 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 529, limit := 649 }) := by cbv

theorem type65_decoded :
    funcType { bytes := artifactBytes, pos := 529, limit := 649 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 539, limit := 649 }) := by cbv

theorem type66_decoded :
    funcType { bytes := artifactBytes, pos := 539, limit := 649 } =
      .ok (Cache.raw.types[66]!, { bytes := artifactBytes, pos := 549, limit := 649 }) := by cbv

theorem type67_decoded :
    funcType { bytes := artifactBytes, pos := 549, limit := 649 } =
      .ok (Cache.raw.types[67]!, { bytes := artifactBytes, pos := 561, limit := 649 }) := by cbv

theorem type68_decoded :
    funcType { bytes := artifactBytes, pos := 561, limit := 649 } =
      .ok (Cache.raw.types[68]!, { bytes := artifactBytes, pos := 572, limit := 649 }) := by cbv

theorem type69_decoded :
    funcType { bytes := artifactBytes, pos := 572, limit := 649 } =
      .ok (Cache.raw.types[69]!, { bytes := artifactBytes, pos := 600, limit := 649 }) := by cbv

theorem type70_decoded :
    funcType { bytes := artifactBytes, pos := 600, limit := 649 } =
      .ok (Cache.raw.types[70]!, { bytes := artifactBytes, pos := 632, limit := 649 }) := by cbv

theorem type71_decoded :
    funcType { bytes := artifactBytes, pos := 632, limit := 649 } =
      .ok (Cache.raw.types[71]!, { bytes := artifactBytes, pos := 637, limit := 649 }) := by cbv

theorem type72_decoded :
    funcType { bytes := artifactBytes, pos := 637, limit := 649 } =
      .ok (Cache.raw.types[72]!, { bytes := artifactBytes, pos := 640, limit := 649 }) := by cbv

theorem type73_decoded :
    funcType { bytes := artifactBytes, pos := 640, limit := 649 } =
      .ok (Cache.raw.types[73]!, { bytes := artifactBytes, pos := 645, limit := 649 }) := by cbv

theorem type74_decoded :
    funcType { bytes := artifactBytes, pos := 645, limit := 649 } =
      .ok (Cache.raw.types[74]!, { bytes := artifactBytes, pos := 649, limit := 649 }) := by cbv

theorem types_tail75_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 649, limit := 649 } =
      .ok (Cache.raw.types.drop 75, { bytes := artifactBytes, pos := 649, limit := 649 }) := by rfl

theorem types_tail74_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 645, limit := 649 } =
      .ok (Cache.raw.types.drop 74, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type74_decoded types_tail75_decoded

theorem types_tail73_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 640, limit := 649 } =
      .ok (Cache.raw.types.drop 73, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type73_decoded types_tail74_decoded

theorem types_tail72_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 637, limit := 649 } =
      .ok (Cache.raw.types.drop 72, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type72_decoded types_tail73_decoded

theorem types_tail71_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 632, limit := 649 } =
      .ok (Cache.raw.types.drop 71, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type71_decoded types_tail72_decoded

theorem types_tail70_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 600, limit := 649 } =
      .ok (Cache.raw.types.drop 70, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type70_decoded types_tail71_decoded

theorem types_tail69_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 572, limit := 649 } =
      .ok (Cache.raw.types.drop 69, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type69_decoded types_tail70_decoded

theorem types_tail68_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 561, limit := 649 } =
      .ok (Cache.raw.types.drop 68, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type68_decoded types_tail69_decoded

theorem types_tail67_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 549, limit := 649 } =
      .ok (Cache.raw.types.drop 67, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type67_decoded types_tail68_decoded

theorem types_tail66_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 539, limit := 649 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type66_decoded types_tail67_decoded

theorem types_tail65_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 529, limit := 649 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type65_decoded types_tail66_decoded

theorem types_tail64_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 519, limit := 649 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type64_decoded types_tail65_decoded

theorem types_tail63_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 509, limit := 649 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type63_decoded types_tail64_decoded

theorem types_tail62_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 500, limit := 649 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type62_decoded types_tail63_decoded

theorem types_tail61_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 491, limit := 649 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type61_decoded types_tail62_decoded

theorem types_tail60_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 481, limit := 649 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type60_decoded types_tail61_decoded

theorem types_tail59_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 471, limit := 649 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type59_decoded types_tail60_decoded

theorem types_tail58_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 463, limit := 649 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type58_decoded types_tail59_decoded

theorem types_tail57_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 455, limit := 649 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type57_decoded types_tail58_decoded

theorem types_tail56_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 447, limit := 649 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type56_decoded types_tail57_decoded

theorem types_tail55_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 439, limit := 649 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type55_decoded types_tail56_decoded

theorem types_tail54_decoded :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 422, limit := 649 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type54_decoded types_tail55_decoded

theorem types_tail53_decoded :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 413, limit := 649 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type53_decoded types_tail54_decoded

theorem types_tail52_decoded :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 407, limit := 649 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type52_decoded types_tail53_decoded

theorem types_tail51_decoded :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 401, limit := 649 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type51_decoded types_tail52_decoded

theorem types_tail50_decoded :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 389, limit := 649 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type50_decoded types_tail51_decoded

theorem types_tail49_decoded :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 377, limit := 649 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50_decoded

theorem types_tail48_decoded :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 365, limit := 649 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49_decoded

theorem types_tail47_decoded :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 353, limit := 649 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48_decoded

theorem types_tail46_decoded :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 343, limit := 649 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47_decoded

theorem types_tail45_decoded :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 333, limit := 649 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46_decoded

theorem types_tail44_decoded :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 328, limit := 649 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 323, limit := 649 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 318, limit := 649 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 313, limit := 649 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 301, limit := 649 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 289, limit := 649 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 274, limit := 649 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 263, limit := 649 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 254, limit := 649 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37_decoded

theorem types_tail35_decoded :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 245, limit := 649 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 238, limit := 649 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 229, limit := 649 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 220, limit := 649 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 211, limit := 649 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 203, limit := 649 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 195, limit := 649 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 189, limit := 649 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 181, limit := 649 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 175, limit := 649 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 167, limit := 649 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop funcType 51 { bytes := artifactBytes, pos := 159, limit := 649 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop funcType 52 { bytes := artifactBytes, pos := 152, limit := 649 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop funcType 53 { bytes := artifactBytes, pos := 147, limit := 649 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop funcType 54 { bytes := artifactBytes, pos := 141, limit := 649 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 55 { bytes := artifactBytes, pos := 136, limit := 649 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21_decoded

theorem types_tail19_decoded :
    Internal.vectorLoop funcType 56 { bytes := artifactBytes, pos := 131, limit := 649 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 57 { bytes := artifactBytes, pos := 123, limit := 649 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 58 { bytes := artifactBytes, pos := 115, limit := 649 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 59 { bytes := artifactBytes, pos := 107, limit := 649 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 60 { bytes := artifactBytes, pos := 101, limit := 649 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 61 { bytes := artifactBytes, pos := 95, limit := 649 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 62 { bytes := artifactBytes, pos := 87, limit := 649 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 63 { bytes := artifactBytes, pos := 81, limit := 649 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 64 { bytes := artifactBytes, pos := 75, limit := 649 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 65 { bytes := artifactBytes, pos := 69, limit := 649 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 66 { bytes := artifactBytes, pos := 61, limit := 649 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 67 { bytes := artifactBytes, pos := 56, limit := 649 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 68 { bytes := artifactBytes, pos := 50, limit := 649 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 69 { bytes := artifactBytes, pos := 45, limit := 649 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 70 { bytes := artifactBytes, pos := 40, limit := 649 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 71 { bytes := artifactBytes, pos := 35, limit := 649 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop funcType 72 { bytes := artifactBytes, pos := 27, limit := 649 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 73 { bytes := artifactBytes, pos := 22, limit := 649 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 74 { bytes := artifactBytes, pos := 17, limit := 649 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 75 { bytes := artifactBytes, pos := 12, limit := 649 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 649 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 649, limit := 649 }) := by
  refine vector_eq_of_parts (length := 75)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 649 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded


end Project.EulerOutwardFaceStep.Artifact
