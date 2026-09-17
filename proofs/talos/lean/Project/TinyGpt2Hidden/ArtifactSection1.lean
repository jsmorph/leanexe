import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem types_item0 :
    funcType { bytes := artifactBytes, pos := 12, limit := 819 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 20, limit := 819 }) := by cbv

theorem types_item1 :
    funcType { bytes := artifactBytes, pos := 20, limit := 819 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 28, limit := 819 }) := by cbv

theorem types_item2 :
    funcType { bytes := artifactBytes, pos := 28, limit := 819 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 36, limit := 819 }) := by cbv

theorem types_item3 :
    funcType { bytes := artifactBytes, pos := 36, limit := 819 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 44, limit := 819 }) := by cbv

theorem types_item4 :
    funcType { bytes := artifactBytes, pos := 44, limit := 819 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 59, limit := 819 }) := by cbv

theorem types_item5 :
    funcType { bytes := artifactBytes, pos := 59, limit := 819 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 69, limit := 819 }) := by cbv

theorem types_item6 :
    funcType { bytes := artifactBytes, pos := 69, limit := 819 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 73, limit := 819 }) := by cbv

theorem types_item7 :
    funcType { bytes := artifactBytes, pos := 73, limit := 819 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 77, limit := 819 }) := by cbv

theorem types_item8 :
    funcType { bytes := artifactBytes, pos := 77, limit := 819 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 88, limit := 819 }) := by cbv

theorem types_item9 :
    funcType { bytes := artifactBytes, pos := 88, limit := 819 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 96, limit := 819 }) := by cbv

theorem types_item10 :
    funcType { bytes := artifactBytes, pos := 96, limit := 819 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 104, limit := 819 }) := by cbv

theorem types_item11 :
    funcType { bytes := artifactBytes, pos := 104, limit := 819 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 112, limit := 819 }) := by cbv

theorem types_item12 :
    funcType { bytes := artifactBytes, pos := 112, limit := 819 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 132, limit := 819 }) := by cbv

theorem types_item13 :
    funcType { bytes := artifactBytes, pos := 132, limit := 819 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 141, limit := 819 }) := by cbv

theorem types_item14 :
    funcType { bytes := artifactBytes, pos := 141, limit := 819 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 150, limit := 819 }) := by cbv

theorem types_item15 :
    funcType { bytes := artifactBytes, pos := 150, limit := 819 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 159, limit := 819 }) := by cbv

theorem types_item16 :
    funcType { bytes := artifactBytes, pos := 159, limit := 819 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 168, limit := 819 }) := by cbv

theorem types_item17 :
    funcType { bytes := artifactBytes, pos := 168, limit := 819 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 182, limit := 819 }) := by cbv

theorem types_item18 :
    funcType { bytes := artifactBytes, pos := 182, limit := 819 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 186, limit := 819 }) := by cbv

theorem types_item19 :
    funcType { bytes := artifactBytes, pos := 186, limit := 819 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 209, limit := 819 }) := by cbv

theorem types_item20 :
    funcType { bytes := artifactBytes, pos := 209, limit := 819 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 232, limit := 819 }) := by cbv

theorem types_item21 :
    funcType { bytes := artifactBytes, pos := 232, limit := 819 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 255, limit := 819 }) := by cbv

theorem types_item22 :
    funcType { bytes := artifactBytes, pos := 255, limit := 819 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 278, limit := 819 }) := by cbv

theorem types_item23 :
    funcType { bytes := artifactBytes, pos := 278, limit := 819 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 286, limit := 819 }) := by cbv

theorem types_item24 :
    funcType { bytes := artifactBytes, pos := 286, limit := 819 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 298, limit := 819 }) := by cbv

theorem types_item25 :
    funcType { bytes := artifactBytes, pos := 298, limit := 819 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 311, limit := 819 }) := by cbv

theorem types_item26 :
    funcType { bytes := artifactBytes, pos := 311, limit := 819 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 325, limit := 819 }) := by cbv

theorem types_item27 :
    funcType { bytes := artifactBytes, pos := 325, limit := 819 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 329, limit := 819 }) := by cbv

theorem types_item28 :
    funcType { bytes := artifactBytes, pos := 329, limit := 819 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 353, limit := 819 }) := by cbv

theorem types_item29 :
    funcType { bytes := artifactBytes, pos := 353, limit := 819 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 391, limit := 819 }) := by cbv

theorem types_item30 :
    funcType { bytes := artifactBytes, pos := 391, limit := 819 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 395, limit := 819 }) := by cbv

theorem types_item31 :
    funcType { bytes := artifactBytes, pos := 395, limit := 819 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 399, limit := 819 }) := by cbv

theorem types_item32 :
    funcType { bytes := artifactBytes, pos := 399, limit := 819 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 405, limit := 819 }) := by cbv

theorem types_item33 :
    funcType { bytes := artifactBytes, pos := 405, limit := 819 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 413, limit := 819 }) := by cbv

theorem types_item34 :
    funcType { bytes := artifactBytes, pos := 413, limit := 819 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 422, limit := 819 }) := by cbv

theorem types_item35 :
    funcType { bytes := artifactBytes, pos := 422, limit := 819 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 430, limit := 819 }) := by cbv

theorem types_item36 :
    funcType { bytes := artifactBytes, pos := 430, limit := 819 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 436, limit := 819 }) := by cbv

theorem types_item37 :
    funcType { bytes := artifactBytes, pos := 436, limit := 819 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 442, limit := 819 }) := by cbv

theorem types_item38 :
    funcType { bytes := artifactBytes, pos := 442, limit := 819 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 447, limit := 819 }) := by cbv

theorem types_item39 :
    funcType { bytes := artifactBytes, pos := 447, limit := 819 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 453, limit := 819 }) := by cbv

theorem types_item40 :
    funcType { bytes := artifactBytes, pos := 453, limit := 819 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 458, limit := 819 }) := by cbv

theorem types_item41 :
    funcType { bytes := artifactBytes, pos := 458, limit := 819 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 466, limit := 819 }) := by cbv

theorem types_item42 :
    funcType { bytes := artifactBytes, pos := 466, limit := 819 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 474, limit := 819 }) := by cbv

theorem types_item43 :
    funcType { bytes := artifactBytes, pos := 474, limit := 819 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 482, limit := 819 }) := by cbv

theorem types_item44 :
    funcType { bytes := artifactBytes, pos := 482, limit := 819 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 495, limit := 819 }) := by cbv

theorem types_item45 :
    funcType { bytes := artifactBytes, pos := 495, limit := 819 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 503, limit := 819 }) := by cbv

theorem types_item46 :
    funcType { bytes := artifactBytes, pos := 503, limit := 819 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 522, limit := 819 }) := by cbv

theorem types_item47 :
    funcType { bytes := artifactBytes, pos := 522, limit := 819 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 531, limit := 819 }) := by cbv

theorem types_item48 :
    funcType { bytes := artifactBytes, pos := 531, limit := 819 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 540, limit := 819 }) := by cbv

theorem types_item49 :
    funcType { bytes := artifactBytes, pos := 540, limit := 819 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 549, limit := 819 }) := by cbv

theorem types_item50 :
    funcType { bytes := artifactBytes, pos := 549, limit := 819 } =
      .ok (Cache.raw.types[50]!, { bytes := artifactBytes, pos := 558, limit := 819 }) := by cbv

theorem types_item51 :
    funcType { bytes := artifactBytes, pos := 558, limit := 819 } =
      .ok (Cache.raw.types[51]!, { bytes := artifactBytes, pos := 571, limit := 819 }) := by cbv

theorem types_item52 :
    funcType { bytes := artifactBytes, pos := 571, limit := 819 } =
      .ok (Cache.raw.types[52]!, { bytes := artifactBytes, pos := 615, limit := 819 }) := by cbv

theorem types_item53 :
    funcType { bytes := artifactBytes, pos := 615, limit := 819 } =
      .ok (Cache.raw.types[53]!, { bytes := artifactBytes, pos := 619, limit := 819 }) := by cbv

theorem types_item54 :
    funcType { bytes := artifactBytes, pos := 619, limit := 819 } =
      .ok (Cache.raw.types[54]!, { bytes := artifactBytes, pos := 623, limit := 819 }) := by cbv

theorem types_item55 :
    funcType { bytes := artifactBytes, pos := 623, limit := 819 } =
      .ok (Cache.raw.types[55]!, { bytes := artifactBytes, pos := 627, limit := 819 }) := by cbv

theorem types_item56 :
    funcType { bytes := artifactBytes, pos := 627, limit := 819 } =
      .ok (Cache.raw.types[56]!, { bytes := artifactBytes, pos := 631, limit := 819 }) := by cbv

theorem types_item57 :
    funcType { bytes := artifactBytes, pos := 631, limit := 819 } =
      .ok (Cache.raw.types[57]!, { bytes := artifactBytes, pos := 648, limit := 819 }) := by cbv

theorem types_item58 :
    funcType { bytes := artifactBytes, pos := 648, limit := 819 } =
      .ok (Cache.raw.types[58]!, { bytes := artifactBytes, pos := 652, limit := 819 }) := by cbv

theorem types_item59 :
    funcType { bytes := artifactBytes, pos := 652, limit := 819 } =
      .ok (Cache.raw.types[59]!, { bytes := artifactBytes, pos := 657, limit := 819 }) := by cbv

theorem types_item60 :
    funcType { bytes := artifactBytes, pos := 657, limit := 819 } =
      .ok (Cache.raw.types[60]!, { bytes := artifactBytes, pos := 662, limit := 819 }) := by cbv

theorem types_item61 :
    funcType { bytes := artifactBytes, pos := 662, limit := 819 } =
      .ok (Cache.raw.types[61]!, { bytes := artifactBytes, pos := 667, limit := 819 }) := by cbv

theorem types_item62 :
    funcType { bytes := artifactBytes, pos := 667, limit := 819 } =
      .ok (Cache.raw.types[62]!, { bytes := artifactBytes, pos := 672, limit := 819 }) := by cbv

theorem types_item63 :
    funcType { bytes := artifactBytes, pos := 672, limit := 819 } =
      .ok (Cache.raw.types[63]!, { bytes := artifactBytes, pos := 677, limit := 819 }) := by cbv

theorem types_item64 :
    funcType { bytes := artifactBytes, pos := 677, limit := 819 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 682, limit := 819 }) := by cbv

theorem types_item65 :
    funcType { bytes := artifactBytes, pos := 682, limit := 819 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 693, limit := 819 }) := by cbv

theorem types_item66 :
    funcType { bytes := artifactBytes, pos := 693, limit := 819 } =
      .ok (Cache.raw.types[66]!, { bytes := artifactBytes, pos := 708, limit := 819 }) := by cbv

theorem types_item67 :
    funcType { bytes := artifactBytes, pos := 708, limit := 819 } =
      .ok (Cache.raw.types[67]!, { bytes := artifactBytes, pos := 723, limit := 819 }) := by cbv

theorem types_item68 :
    funcType { bytes := artifactBytes, pos := 723, limit := 819 } =
      .ok (Cache.raw.types[68]!, { bytes := artifactBytes, pos := 743, limit := 819 }) := by cbv

theorem types_item69 :
    funcType { bytes := artifactBytes, pos := 743, limit := 819 } =
      .ok (Cache.raw.types[69]!, { bytes := artifactBytes, pos := 760, limit := 819 }) := by cbv

theorem types_item70 :
    funcType { bytes := artifactBytes, pos := 760, limit := 819 } =
      .ok (Cache.raw.types[70]!, { bytes := artifactBytes, pos := 764, limit := 819 }) := by cbv

theorem types_item71 :
    funcType { bytes := artifactBytes, pos := 764, limit := 819 } =
      .ok (Cache.raw.types[71]!, { bytes := artifactBytes, pos := 768, limit := 819 }) := by cbv

theorem types_item72 :
    funcType { bytes := artifactBytes, pos := 768, limit := 819 } =
      .ok (Cache.raw.types[72]!, { bytes := artifactBytes, pos := 785, limit := 819 }) := by cbv

theorem types_item73 :
    funcType { bytes := artifactBytes, pos := 785, limit := 819 } =
      .ok (Cache.raw.types[73]!, { bytes := artifactBytes, pos := 789, limit := 819 }) := by cbv

theorem types_item74 :
    funcType { bytes := artifactBytes, pos := 789, limit := 819 } =
      .ok (Cache.raw.types[74]!, { bytes := artifactBytes, pos := 802, limit := 819 }) := by cbv

theorem types_item75 :
    funcType { bytes := artifactBytes, pos := 802, limit := 819 } =
      .ok (Cache.raw.types[75]!, { bytes := artifactBytes, pos := 807, limit := 819 }) := by cbv

theorem types_item76 :
    funcType { bytes := artifactBytes, pos := 807, limit := 819 } =
      .ok (Cache.raw.types[76]!, { bytes := artifactBytes, pos := 810, limit := 819 }) := by cbv

theorem types_item77 :
    funcType { bytes := artifactBytes, pos := 810, limit := 819 } =
      .ok (Cache.raw.types[77]!, { bytes := artifactBytes, pos := 815, limit := 819 }) := by cbv

theorem types_item78 :
    funcType { bytes := artifactBytes, pos := 815, limit := 819 } =
      .ok (Cache.raw.types[78]!, { bytes := artifactBytes, pos := 819, limit := 819 }) := by cbv

theorem types_tail79 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 819, limit := 819 } =
      .ok (Cache.raw.types.drop 79, { bytes := artifactBytes, pos := 819, limit := 819 }) := by rfl

theorem types_tail78 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 815, limit := 819 } =
      .ok (Cache.raw.types.drop 78, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item78 types_tail79

theorem types_tail77 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 810, limit := 819 } =
      .ok (Cache.raw.types.drop 77, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item77 types_tail78

theorem types_tail76 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 807, limit := 819 } =
      .ok (Cache.raw.types.drop 76, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item76 types_tail77

theorem types_tail75 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 802, limit := 819 } =
      .ok (Cache.raw.types.drop 75, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item75 types_tail76

theorem types_tail74 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 789, limit := 819 } =
      .ok (Cache.raw.types.drop 74, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item74 types_tail75

theorem types_tail73 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 785, limit := 819 } =
      .ok (Cache.raw.types.drop 73, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item73 types_tail74

theorem types_tail72 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 768, limit := 819 } =
      .ok (Cache.raw.types.drop 72, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item72 types_tail73

theorem types_tail71 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 764, limit := 819 } =
      .ok (Cache.raw.types.drop 71, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item71 types_tail72

theorem types_tail70 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 760, limit := 819 } =
      .ok (Cache.raw.types.drop 70, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item70 types_tail71

theorem types_tail69 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 743, limit := 819 } =
      .ok (Cache.raw.types.drop 69, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item69 types_tail70

theorem types_tail68 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 723, limit := 819 } =
      .ok (Cache.raw.types.drop 68, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item68 types_tail69

theorem types_tail67 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 708, limit := 819 } =
      .ok (Cache.raw.types.drop 67, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item67 types_tail68

theorem types_tail66 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 693, limit := 819 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item66 types_tail67

theorem types_tail65 :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 682, limit := 819 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item65 types_tail66

theorem types_tail64 :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 677, limit := 819 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item64 types_tail65

theorem types_tail63 :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 672, limit := 819 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item63 types_tail64

theorem types_tail62 :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 667, limit := 819 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item62 types_tail63

theorem types_tail61 :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 662, limit := 819 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item61 types_tail62

theorem types_tail60 :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 657, limit := 819 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item60 types_tail61

theorem types_tail59 :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 652, limit := 819 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item59 types_tail60

theorem types_tail58 :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 648, limit := 819 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item58 types_tail59

theorem types_tail57 :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 631, limit := 819 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item57 types_tail58

theorem types_tail56 :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 627, limit := 819 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item56 types_tail57

theorem types_tail55 :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 623, limit := 819 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item55 types_tail56

theorem types_tail54 :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 619, limit := 819 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item54 types_tail55

theorem types_tail53 :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 615, limit := 819 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item53 types_tail54

theorem types_tail52 :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 571, limit := 819 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item52 types_tail53

theorem types_tail51 :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 558, limit := 819 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item51 types_tail52

theorem types_tail50 :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 549, limit := 819 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item50 types_tail51

theorem types_tail49 :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 540, limit := 819 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item49 types_tail50

theorem types_tail48 :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 531, limit := 819 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item48 types_tail49

theorem types_tail47 :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 522, limit := 819 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item47 types_tail48

theorem types_tail46 :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 503, limit := 819 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item46 types_tail47

theorem types_tail45 :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 495, limit := 819 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item45 types_tail46

theorem types_tail44 :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 482, limit := 819 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item44 types_tail45

theorem types_tail43 :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 474, limit := 819 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item43 types_tail44

theorem types_tail42 :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 466, limit := 819 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item42 types_tail43

theorem types_tail41 :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 458, limit := 819 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item41 types_tail42

theorem types_tail40 :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 453, limit := 819 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item40 types_tail41

theorem types_tail39 :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 447, limit := 819 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item39 types_tail40

theorem types_tail38 :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 442, limit := 819 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item38 types_tail39

theorem types_tail37 :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 436, limit := 819 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item37 types_tail38

theorem types_tail36 :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 430, limit := 819 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item36 types_tail37

theorem types_tail35 :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 422, limit := 819 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item35 types_tail36

theorem types_tail34 :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 413, limit := 819 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item34 types_tail35

theorem types_tail33 :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 405, limit := 819 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item33 types_tail34

theorem types_tail32 :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 399, limit := 819 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item32 types_tail33

theorem types_tail31 :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 395, limit := 819 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item31 types_tail32

theorem types_tail30 :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 391, limit := 819 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item30 types_tail31

theorem types_tail29 :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 353, limit := 819 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item29 types_tail30

theorem types_tail28 :
    Internal.vectorLoop funcType 51 { bytes := artifactBytes, pos := 329, limit := 819 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item28 types_tail29

theorem types_tail27 :
    Internal.vectorLoop funcType 52 { bytes := artifactBytes, pos := 325, limit := 819 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item27 types_tail28

theorem types_tail26 :
    Internal.vectorLoop funcType 53 { bytes := artifactBytes, pos := 311, limit := 819 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item26 types_tail27

theorem types_tail25 :
    Internal.vectorLoop funcType 54 { bytes := artifactBytes, pos := 298, limit := 819 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item25 types_tail26

theorem types_tail24 :
    Internal.vectorLoop funcType 55 { bytes := artifactBytes, pos := 286, limit := 819 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item24 types_tail25

theorem types_tail23 :
    Internal.vectorLoop funcType 56 { bytes := artifactBytes, pos := 278, limit := 819 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item23 types_tail24

theorem types_tail22 :
    Internal.vectorLoop funcType 57 { bytes := artifactBytes, pos := 255, limit := 819 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item22 types_tail23

theorem types_tail21 :
    Internal.vectorLoop funcType 58 { bytes := artifactBytes, pos := 232, limit := 819 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item21 types_tail22

theorem types_tail20 :
    Internal.vectorLoop funcType 59 { bytes := artifactBytes, pos := 209, limit := 819 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item20 types_tail21

theorem types_tail19 :
    Internal.vectorLoop funcType 60 { bytes := artifactBytes, pos := 186, limit := 819 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item19 types_tail20

theorem types_tail18 :
    Internal.vectorLoop funcType 61 { bytes := artifactBytes, pos := 182, limit := 819 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item18 types_tail19

theorem types_tail17 :
    Internal.vectorLoop funcType 62 { bytes := artifactBytes, pos := 168, limit := 819 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item17 types_tail18

theorem types_tail16 :
    Internal.vectorLoop funcType 63 { bytes := artifactBytes, pos := 159, limit := 819 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item16 types_tail17

theorem types_tail15 :
    Internal.vectorLoop funcType 64 { bytes := artifactBytes, pos := 150, limit := 819 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item15 types_tail16

theorem types_tail14 :
    Internal.vectorLoop funcType 65 { bytes := artifactBytes, pos := 141, limit := 819 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item14 types_tail15

theorem types_tail13 :
    Internal.vectorLoop funcType 66 { bytes := artifactBytes, pos := 132, limit := 819 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item13 types_tail14

theorem types_tail12 :
    Internal.vectorLoop funcType 67 { bytes := artifactBytes, pos := 112, limit := 819 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item12 types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 68 { bytes := artifactBytes, pos := 104, limit := 819 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item11 types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 69 { bytes := artifactBytes, pos := 96, limit := 819 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item10 types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 70 { bytes := artifactBytes, pos := 88, limit := 819 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item9 types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 71 { bytes := artifactBytes, pos := 77, limit := 819 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item8 types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 72 { bytes := artifactBytes, pos := 73, limit := 819 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item7 types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 73 { bytes := artifactBytes, pos := 69, limit := 819 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item6 types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 74 { bytes := artifactBytes, pos := 59, limit := 819 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item5 types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 75 { bytes := artifactBytes, pos := 44, limit := 819 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item4 types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 76 { bytes := artifactBytes, pos := 36, limit := 819 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item3 types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 77 { bytes := artifactBytes, pos := 28, limit := 819 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item2 types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 78 { bytes := artifactBytes, pos := 20, limit := 819 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item1 types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 79 { bytes := artifactBytes, pos := 12, limit := 819 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  exact vectorLoop_eq_cons types_item0 types_tail1

theorem types_vector :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 819 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 819, limit := 819 }) := by
  refine vector_eq_of_parts (length := 79) (itemsStart := { bytes := artifactBytes, pos := 12, limit := 819 }) ?_ ?_ types_tail0
  · cbv
  · decide

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 16006 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 819, limit := 16006 }) := by
  refine sized_eq_of_parts (size := 808) (payload := { bytes := artifactBytes, pos := 11, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 819, limit := 819 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector
  · rfl

#print axioms types_section_decoded
end Project.TinyGpt2Hidden.Artifact
