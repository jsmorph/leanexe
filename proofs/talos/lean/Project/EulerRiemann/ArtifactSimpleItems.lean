import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionTypeIndices_item0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1026, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 1027, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1027, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 1028, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1028, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 1029, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1029, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 1030, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1030, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 1031, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1031, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 1032, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1032, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 1033, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1033, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 1034, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1034, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 1035, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1035, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 1036, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1036, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 1037, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1037, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 1038, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1038, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 1039, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1039, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 1040, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1040, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 1041, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1041, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 1042, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1042, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 1043, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1043, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 1044, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1044, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 1045, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1045, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 1046, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1046, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 1047, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1047, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 1048, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1048, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 1049, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1049, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 1050, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1050, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 1051, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1051, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 1052, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1052, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 1053, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1053, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 1054, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1054, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 1055, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1055, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 1056, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1056, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 1057, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1057, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 1058, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1058, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 1059, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1059, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 1060, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1060, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 1061, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1061, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 1062, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1062, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 1063, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1063, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 1064, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1064, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 1065, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1065, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 1066, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1066, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 1067, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1067, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 1068, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1068, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 1069, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item43_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1069, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 1070, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item44_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1070, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 1071, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item45_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1071, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 1072, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item46_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1072, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 1073, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item47_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1073, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 1074, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item48_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1074, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 1075, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item49_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1075, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 1076, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item50_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1076, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[50]!, { bytes := artifactBytes, pos := 1077, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item51_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1077, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[51]!, { bytes := artifactBytes, pos := 1078, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item52_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1078, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[52]!, { bytes := artifactBytes, pos := 1079, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item53_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1079, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[53]!, { bytes := artifactBytes, pos := 1080, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item54_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1080, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[54]!, { bytes := artifactBytes, pos := 1081, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item55_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1081, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[55]!, { bytes := artifactBytes, pos := 1082, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item56_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1082, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[56]!, { bytes := artifactBytes, pos := 1083, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item57_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1083, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[57]!, { bytes := artifactBytes, pos := 1084, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item58_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1084, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[58]!, { bytes := artifactBytes, pos := 1085, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item59_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1085, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[59]!, { bytes := artifactBytes, pos := 1086, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item60_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1086, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[60]!, { bytes := artifactBytes, pos := 1087, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item61_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1087, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[61]!, { bytes := artifactBytes, pos := 1088, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item62_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1088, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[62]!, { bytes := artifactBytes, pos := 1089, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item63_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1089, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[63]!, { bytes := artifactBytes, pos := 1090, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item64_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1090, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[64]!, { bytes := artifactBytes, pos := 1091, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item65_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1091, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[65]!, { bytes := artifactBytes, pos := 1092, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item66_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1092, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[66]!, { bytes := artifactBytes, pos := 1093, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item67_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1093, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[67]!, { bytes := artifactBytes, pos := 1094, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item68_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1094, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[68]!, { bytes := artifactBytes, pos := 1095, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item69_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1095, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[69]!, { bytes := artifactBytes, pos := 1096, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item70_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1096, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[70]!, { bytes := artifactBytes, pos := 1097, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item71_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1097, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[71]!, { bytes := artifactBytes, pos := 1098, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item72_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1098, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[72]!, { bytes := artifactBytes, pos := 1099, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item73_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1099, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[73]!, { bytes := artifactBytes, pos := 1100, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item74_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1100, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[74]!, { bytes := artifactBytes, pos := 1101, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item75_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1101, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[75]!, { bytes := artifactBytes, pos := 1102, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item76_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1102, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[76]!, { bytes := artifactBytes, pos := 1103, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item77_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1103, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[77]!, { bytes := artifactBytes, pos := 1104, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item78_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1104, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[78]!, { bytes := artifactBytes, pos := 1105, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item79_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1105, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[79]!, { bytes := artifactBytes, pos := 1106, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item80_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1106, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[80]!, { bytes := artifactBytes, pos := 1107, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item81_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1107, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[81]!, { bytes := artifactBytes, pos := 1108, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item82_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1108, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[82]!, { bytes := artifactBytes, pos := 1109, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item83_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1109, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[83]!, { bytes := artifactBytes, pos := 1110, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item84_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1110, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[84]!, { bytes := artifactBytes, pos := 1111, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item85_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1111, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[85]!, { bytes := artifactBytes, pos := 1112, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item86_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1112, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[86]!, { bytes := artifactBytes, pos := 1113, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item87_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1113, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[87]!, { bytes := artifactBytes, pos := 1114, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item88_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1114, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[88]!, { bytes := artifactBytes, pos := 1115, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item89_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1115, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[89]!, { bytes := artifactBytes, pos := 1116, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item90_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1116, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[90]!, { bytes := artifactBytes, pos := 1117, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item91_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1117, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[91]!, { bytes := artifactBytes, pos := 1118, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item92_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1118, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[92]!, { bytes := artifactBytes, pos := 1119, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item93_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1119, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[93]!, { bytes := artifactBytes, pos := 1120, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item94_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1120, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[94]!, { bytes := artifactBytes, pos := 1121, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item95_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1121, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[95]!, { bytes := artifactBytes, pos := 1122, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item96_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1122, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[96]!, { bytes := artifactBytes, pos := 1123, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item97_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1123, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[97]!, { bytes := artifactBytes, pos := 1124, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item98_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1124, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[98]!, { bytes := artifactBytes, pos := 1125, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item99_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1125, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[99]!, { bytes := artifactBytes, pos := 1126, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item100_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1126, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[100]!, { bytes := artifactBytes, pos := 1127, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item101_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1127, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[101]!, { bytes := artifactBytes, pos := 1128, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item102_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1128, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[102]!, { bytes := artifactBytes, pos := 1129, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item103_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1129, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[103]!, { bytes := artifactBytes, pos := 1130, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item104_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1130, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[104]!, { bytes := artifactBytes, pos := 1131, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item105_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1131, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[105]!, { bytes := artifactBytes, pos := 1132, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item106_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1132, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[106]!, { bytes := artifactBytes, pos := 1133, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_item107_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1133, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices[107]!, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  cbv

theorem functionTypeIndices_tail108_decoded :
    Internal.vectorLoop (Leb.u32) 0 { bytes := artifactBytes, pos := 1134, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 108, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by rfl

theorem functionTypeIndices_tail107_decoded :
    Internal.vectorLoop (Leb.u32) 1 { bytes := artifactBytes, pos := 1133, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 107, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item107_decoded functionTypeIndices_tail108_decoded

theorem functionTypeIndices_tail106_decoded :
    Internal.vectorLoop (Leb.u32) 2 { bytes := artifactBytes, pos := 1132, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 106, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item106_decoded functionTypeIndices_tail107_decoded

theorem functionTypeIndices_tail105_decoded :
    Internal.vectorLoop (Leb.u32) 3 { bytes := artifactBytes, pos := 1131, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 105, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item105_decoded functionTypeIndices_tail106_decoded

theorem functionTypeIndices_tail104_decoded :
    Internal.vectorLoop (Leb.u32) 4 { bytes := artifactBytes, pos := 1130, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 104, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item104_decoded functionTypeIndices_tail105_decoded

theorem functionTypeIndices_tail103_decoded :
    Internal.vectorLoop (Leb.u32) 5 { bytes := artifactBytes, pos := 1129, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 103, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item103_decoded functionTypeIndices_tail104_decoded

theorem functionTypeIndices_tail102_decoded :
    Internal.vectorLoop (Leb.u32) 6 { bytes := artifactBytes, pos := 1128, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 102, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item102_decoded functionTypeIndices_tail103_decoded

theorem functionTypeIndices_tail101_decoded :
    Internal.vectorLoop (Leb.u32) 7 { bytes := artifactBytes, pos := 1127, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 101, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item101_decoded functionTypeIndices_tail102_decoded

theorem functionTypeIndices_tail100_decoded :
    Internal.vectorLoop (Leb.u32) 8 { bytes := artifactBytes, pos := 1126, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 100, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item100_decoded functionTypeIndices_tail101_decoded

theorem functionTypeIndices_tail99_decoded :
    Internal.vectorLoop (Leb.u32) 9 { bytes := artifactBytes, pos := 1125, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 99, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item99_decoded functionTypeIndices_tail100_decoded

theorem functionTypeIndices_tail98_decoded :
    Internal.vectorLoop (Leb.u32) 10 { bytes := artifactBytes, pos := 1124, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 98, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item98_decoded functionTypeIndices_tail99_decoded

theorem functionTypeIndices_tail97_decoded :
    Internal.vectorLoop (Leb.u32) 11 { bytes := artifactBytes, pos := 1123, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 97, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item97_decoded functionTypeIndices_tail98_decoded

theorem functionTypeIndices_tail96_decoded :
    Internal.vectorLoop (Leb.u32) 12 { bytes := artifactBytes, pos := 1122, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 96, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item96_decoded functionTypeIndices_tail97_decoded

theorem functionTypeIndices_tail95_decoded :
    Internal.vectorLoop (Leb.u32) 13 { bytes := artifactBytes, pos := 1121, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 95, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item95_decoded functionTypeIndices_tail96_decoded

theorem functionTypeIndices_tail94_decoded :
    Internal.vectorLoop (Leb.u32) 14 { bytes := artifactBytes, pos := 1120, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 94, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item94_decoded functionTypeIndices_tail95_decoded

theorem functionTypeIndices_tail93_decoded :
    Internal.vectorLoop (Leb.u32) 15 { bytes := artifactBytes, pos := 1119, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 93, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item93_decoded functionTypeIndices_tail94_decoded

theorem functionTypeIndices_tail92_decoded :
    Internal.vectorLoop (Leb.u32) 16 { bytes := artifactBytes, pos := 1118, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 92, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item92_decoded functionTypeIndices_tail93_decoded

theorem functionTypeIndices_tail91_decoded :
    Internal.vectorLoop (Leb.u32) 17 { bytes := artifactBytes, pos := 1117, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 91, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item91_decoded functionTypeIndices_tail92_decoded

theorem functionTypeIndices_tail90_decoded :
    Internal.vectorLoop (Leb.u32) 18 { bytes := artifactBytes, pos := 1116, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 90, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item90_decoded functionTypeIndices_tail91_decoded

theorem functionTypeIndices_tail89_decoded :
    Internal.vectorLoop (Leb.u32) 19 { bytes := artifactBytes, pos := 1115, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 89, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item89_decoded functionTypeIndices_tail90_decoded

theorem functionTypeIndices_tail88_decoded :
    Internal.vectorLoop (Leb.u32) 20 { bytes := artifactBytes, pos := 1114, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 88, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item88_decoded functionTypeIndices_tail89_decoded

theorem functionTypeIndices_tail87_decoded :
    Internal.vectorLoop (Leb.u32) 21 { bytes := artifactBytes, pos := 1113, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 87, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item87_decoded functionTypeIndices_tail88_decoded

theorem functionTypeIndices_tail86_decoded :
    Internal.vectorLoop (Leb.u32) 22 { bytes := artifactBytes, pos := 1112, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 86, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item86_decoded functionTypeIndices_tail87_decoded

theorem functionTypeIndices_tail85_decoded :
    Internal.vectorLoop (Leb.u32) 23 { bytes := artifactBytes, pos := 1111, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 85, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item85_decoded functionTypeIndices_tail86_decoded

theorem functionTypeIndices_tail84_decoded :
    Internal.vectorLoop (Leb.u32) 24 { bytes := artifactBytes, pos := 1110, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 84, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item84_decoded functionTypeIndices_tail85_decoded

theorem functionTypeIndices_tail83_decoded :
    Internal.vectorLoop (Leb.u32) 25 { bytes := artifactBytes, pos := 1109, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 83, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item83_decoded functionTypeIndices_tail84_decoded

theorem functionTypeIndices_tail82_decoded :
    Internal.vectorLoop (Leb.u32) 26 { bytes := artifactBytes, pos := 1108, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 82, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item82_decoded functionTypeIndices_tail83_decoded

theorem functionTypeIndices_tail81_decoded :
    Internal.vectorLoop (Leb.u32) 27 { bytes := artifactBytes, pos := 1107, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 81, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item81_decoded functionTypeIndices_tail82_decoded

theorem functionTypeIndices_tail80_decoded :
    Internal.vectorLoop (Leb.u32) 28 { bytes := artifactBytes, pos := 1106, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 80, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item80_decoded functionTypeIndices_tail81_decoded

theorem functionTypeIndices_tail79_decoded :
    Internal.vectorLoop (Leb.u32) 29 { bytes := artifactBytes, pos := 1105, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 79, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item79_decoded functionTypeIndices_tail80_decoded

theorem functionTypeIndices_tail78_decoded :
    Internal.vectorLoop (Leb.u32) 30 { bytes := artifactBytes, pos := 1104, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 78, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item78_decoded functionTypeIndices_tail79_decoded

theorem functionTypeIndices_tail77_decoded :
    Internal.vectorLoop (Leb.u32) 31 { bytes := artifactBytes, pos := 1103, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 77, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item77_decoded functionTypeIndices_tail78_decoded

theorem functionTypeIndices_tail76_decoded :
    Internal.vectorLoop (Leb.u32) 32 { bytes := artifactBytes, pos := 1102, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 76, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item76_decoded functionTypeIndices_tail77_decoded

theorem functionTypeIndices_tail75_decoded :
    Internal.vectorLoop (Leb.u32) 33 { bytes := artifactBytes, pos := 1101, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 75, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item75_decoded functionTypeIndices_tail76_decoded

theorem functionTypeIndices_tail74_decoded :
    Internal.vectorLoop (Leb.u32) 34 { bytes := artifactBytes, pos := 1100, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 74, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item74_decoded functionTypeIndices_tail75_decoded

theorem functionTypeIndices_tail73_decoded :
    Internal.vectorLoop (Leb.u32) 35 { bytes := artifactBytes, pos := 1099, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 73, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item73_decoded functionTypeIndices_tail74_decoded

theorem functionTypeIndices_tail72_decoded :
    Internal.vectorLoop (Leb.u32) 36 { bytes := artifactBytes, pos := 1098, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 72, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item72_decoded functionTypeIndices_tail73_decoded

theorem functionTypeIndices_tail71_decoded :
    Internal.vectorLoop (Leb.u32) 37 { bytes := artifactBytes, pos := 1097, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 71, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item71_decoded functionTypeIndices_tail72_decoded

theorem functionTypeIndices_tail70_decoded :
    Internal.vectorLoop (Leb.u32) 38 { bytes := artifactBytes, pos := 1096, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 70, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item70_decoded functionTypeIndices_tail71_decoded

theorem functionTypeIndices_tail69_decoded :
    Internal.vectorLoop (Leb.u32) 39 { bytes := artifactBytes, pos := 1095, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 69, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item69_decoded functionTypeIndices_tail70_decoded

theorem functionTypeIndices_tail68_decoded :
    Internal.vectorLoop (Leb.u32) 40 { bytes := artifactBytes, pos := 1094, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 68, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item68_decoded functionTypeIndices_tail69_decoded

theorem functionTypeIndices_tail67_decoded :
    Internal.vectorLoop (Leb.u32) 41 { bytes := artifactBytes, pos := 1093, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 67, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item67_decoded functionTypeIndices_tail68_decoded

theorem functionTypeIndices_tail66_decoded :
    Internal.vectorLoop (Leb.u32) 42 { bytes := artifactBytes, pos := 1092, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 66, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item66_decoded functionTypeIndices_tail67_decoded

theorem functionTypeIndices_tail65_decoded :
    Internal.vectorLoop (Leb.u32) 43 { bytes := artifactBytes, pos := 1091, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 65, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item65_decoded functionTypeIndices_tail66_decoded

theorem functionTypeIndices_tail64_decoded :
    Internal.vectorLoop (Leb.u32) 44 { bytes := artifactBytes, pos := 1090, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 64, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item64_decoded functionTypeIndices_tail65_decoded

theorem functionTypeIndices_tail63_decoded :
    Internal.vectorLoop (Leb.u32) 45 { bytes := artifactBytes, pos := 1089, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 63, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item63_decoded functionTypeIndices_tail64_decoded

theorem functionTypeIndices_tail62_decoded :
    Internal.vectorLoop (Leb.u32) 46 { bytes := artifactBytes, pos := 1088, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 62, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item62_decoded functionTypeIndices_tail63_decoded

theorem functionTypeIndices_tail61_decoded :
    Internal.vectorLoop (Leb.u32) 47 { bytes := artifactBytes, pos := 1087, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 61, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item61_decoded functionTypeIndices_tail62_decoded

theorem functionTypeIndices_tail60_decoded :
    Internal.vectorLoop (Leb.u32) 48 { bytes := artifactBytes, pos := 1086, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 60, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item60_decoded functionTypeIndices_tail61_decoded

theorem functionTypeIndices_tail59_decoded :
    Internal.vectorLoop (Leb.u32) 49 { bytes := artifactBytes, pos := 1085, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 59, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item59_decoded functionTypeIndices_tail60_decoded

theorem functionTypeIndices_tail58_decoded :
    Internal.vectorLoop (Leb.u32) 50 { bytes := artifactBytes, pos := 1084, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 58, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item58_decoded functionTypeIndices_tail59_decoded

theorem functionTypeIndices_tail57_decoded :
    Internal.vectorLoop (Leb.u32) 51 { bytes := artifactBytes, pos := 1083, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 57, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item57_decoded functionTypeIndices_tail58_decoded

theorem functionTypeIndices_tail56_decoded :
    Internal.vectorLoop (Leb.u32) 52 { bytes := artifactBytes, pos := 1082, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 56, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item56_decoded functionTypeIndices_tail57_decoded

theorem functionTypeIndices_tail55_decoded :
    Internal.vectorLoop (Leb.u32) 53 { bytes := artifactBytes, pos := 1081, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 55, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item55_decoded functionTypeIndices_tail56_decoded

theorem functionTypeIndices_tail54_decoded :
    Internal.vectorLoop (Leb.u32) 54 { bytes := artifactBytes, pos := 1080, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 54, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item54_decoded functionTypeIndices_tail55_decoded

theorem functionTypeIndices_tail53_decoded :
    Internal.vectorLoop (Leb.u32) 55 { bytes := artifactBytes, pos := 1079, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 53, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item53_decoded functionTypeIndices_tail54_decoded

theorem functionTypeIndices_tail52_decoded :
    Internal.vectorLoop (Leb.u32) 56 { bytes := artifactBytes, pos := 1078, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 52, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item52_decoded functionTypeIndices_tail53_decoded

theorem functionTypeIndices_tail51_decoded :
    Internal.vectorLoop (Leb.u32) 57 { bytes := artifactBytes, pos := 1077, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 51, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item51_decoded functionTypeIndices_tail52_decoded

theorem functionTypeIndices_tail50_decoded :
    Internal.vectorLoop (Leb.u32) 58 { bytes := artifactBytes, pos := 1076, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 50, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item50_decoded functionTypeIndices_tail51_decoded

theorem functionTypeIndices_tail49_decoded :
    Internal.vectorLoop (Leb.u32) 59 { bytes := artifactBytes, pos := 1075, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 49, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item49_decoded functionTypeIndices_tail50_decoded

theorem functionTypeIndices_tail48_decoded :
    Internal.vectorLoop (Leb.u32) 60 { bytes := artifactBytes, pos := 1074, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 48, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item48_decoded functionTypeIndices_tail49_decoded

theorem functionTypeIndices_tail47_decoded :
    Internal.vectorLoop (Leb.u32) 61 { bytes := artifactBytes, pos := 1073, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 47, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item47_decoded functionTypeIndices_tail48_decoded

theorem functionTypeIndices_tail46_decoded :
    Internal.vectorLoop (Leb.u32) 62 { bytes := artifactBytes, pos := 1072, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 46, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item46_decoded functionTypeIndices_tail47_decoded

theorem functionTypeIndices_tail45_decoded :
    Internal.vectorLoop (Leb.u32) 63 { bytes := artifactBytes, pos := 1071, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 45, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item45_decoded functionTypeIndices_tail46_decoded

theorem functionTypeIndices_tail44_decoded :
    Internal.vectorLoop (Leb.u32) 64 { bytes := artifactBytes, pos := 1070, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 44, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item44_decoded functionTypeIndices_tail45_decoded

theorem functionTypeIndices_tail43_decoded :
    Internal.vectorLoop (Leb.u32) 65 { bytes := artifactBytes, pos := 1069, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item43_decoded functionTypeIndices_tail44_decoded

theorem functionTypeIndices_tail42_decoded :
    Internal.vectorLoop (Leb.u32) 66 { bytes := artifactBytes, pos := 1068, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item42_decoded functionTypeIndices_tail43_decoded

theorem functionTypeIndices_tail41_decoded :
    Internal.vectorLoop (Leb.u32) 67 { bytes := artifactBytes, pos := 1067, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item41_decoded functionTypeIndices_tail42_decoded

theorem functionTypeIndices_tail40_decoded :
    Internal.vectorLoop (Leb.u32) 68 { bytes := artifactBytes, pos := 1066, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item40_decoded functionTypeIndices_tail41_decoded

theorem functionTypeIndices_tail39_decoded :
    Internal.vectorLoop (Leb.u32) 69 { bytes := artifactBytes, pos := 1065, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item39_decoded functionTypeIndices_tail40_decoded

theorem functionTypeIndices_tail38_decoded :
    Internal.vectorLoop (Leb.u32) 70 { bytes := artifactBytes, pos := 1064, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item38_decoded functionTypeIndices_tail39_decoded

theorem functionTypeIndices_tail37_decoded :
    Internal.vectorLoop (Leb.u32) 71 { bytes := artifactBytes, pos := 1063, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item37_decoded functionTypeIndices_tail38_decoded

theorem functionTypeIndices_tail36_decoded :
    Internal.vectorLoop (Leb.u32) 72 { bytes := artifactBytes, pos := 1062, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item36_decoded functionTypeIndices_tail37_decoded

theorem functionTypeIndices_tail35_decoded :
    Internal.vectorLoop (Leb.u32) 73 { bytes := artifactBytes, pos := 1061, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item35_decoded functionTypeIndices_tail36_decoded

theorem functionTypeIndices_tail34_decoded :
    Internal.vectorLoop (Leb.u32) 74 { bytes := artifactBytes, pos := 1060, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item34_decoded functionTypeIndices_tail35_decoded

theorem functionTypeIndices_tail33_decoded :
    Internal.vectorLoop (Leb.u32) 75 { bytes := artifactBytes, pos := 1059, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item33_decoded functionTypeIndices_tail34_decoded

theorem functionTypeIndices_tail32_decoded :
    Internal.vectorLoop (Leb.u32) 76 { bytes := artifactBytes, pos := 1058, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item32_decoded functionTypeIndices_tail33_decoded

theorem functionTypeIndices_tail31_decoded :
    Internal.vectorLoop (Leb.u32) 77 { bytes := artifactBytes, pos := 1057, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item31_decoded functionTypeIndices_tail32_decoded

theorem functionTypeIndices_tail30_decoded :
    Internal.vectorLoop (Leb.u32) 78 { bytes := artifactBytes, pos := 1056, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item30_decoded functionTypeIndices_tail31_decoded

theorem functionTypeIndices_tail29_decoded :
    Internal.vectorLoop (Leb.u32) 79 { bytes := artifactBytes, pos := 1055, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item29_decoded functionTypeIndices_tail30_decoded

theorem functionTypeIndices_tail28_decoded :
    Internal.vectorLoop (Leb.u32) 80 { bytes := artifactBytes, pos := 1054, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item28_decoded functionTypeIndices_tail29_decoded

theorem functionTypeIndices_tail27_decoded :
    Internal.vectorLoop (Leb.u32) 81 { bytes := artifactBytes, pos := 1053, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item27_decoded functionTypeIndices_tail28_decoded

theorem functionTypeIndices_tail26_decoded :
    Internal.vectorLoop (Leb.u32) 82 { bytes := artifactBytes, pos := 1052, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item26_decoded functionTypeIndices_tail27_decoded

theorem functionTypeIndices_tail25_decoded :
    Internal.vectorLoop (Leb.u32) 83 { bytes := artifactBytes, pos := 1051, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item25_decoded functionTypeIndices_tail26_decoded

theorem functionTypeIndices_tail24_decoded :
    Internal.vectorLoop (Leb.u32) 84 { bytes := artifactBytes, pos := 1050, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item24_decoded functionTypeIndices_tail25_decoded

theorem functionTypeIndices_tail23_decoded :
    Internal.vectorLoop (Leb.u32) 85 { bytes := artifactBytes, pos := 1049, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item23_decoded functionTypeIndices_tail24_decoded

theorem functionTypeIndices_tail22_decoded :
    Internal.vectorLoop (Leb.u32) 86 { bytes := artifactBytes, pos := 1048, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item22_decoded functionTypeIndices_tail23_decoded

theorem functionTypeIndices_tail21_decoded :
    Internal.vectorLoop (Leb.u32) 87 { bytes := artifactBytes, pos := 1047, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item21_decoded functionTypeIndices_tail22_decoded

theorem functionTypeIndices_tail20_decoded :
    Internal.vectorLoop (Leb.u32) 88 { bytes := artifactBytes, pos := 1046, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item20_decoded functionTypeIndices_tail21_decoded

theorem functionTypeIndices_tail19_decoded :
    Internal.vectorLoop (Leb.u32) 89 { bytes := artifactBytes, pos := 1045, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item19_decoded functionTypeIndices_tail20_decoded

theorem functionTypeIndices_tail18_decoded :
    Internal.vectorLoop (Leb.u32) 90 { bytes := artifactBytes, pos := 1044, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item18_decoded functionTypeIndices_tail19_decoded

theorem functionTypeIndices_tail17_decoded :
    Internal.vectorLoop (Leb.u32) 91 { bytes := artifactBytes, pos := 1043, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item17_decoded functionTypeIndices_tail18_decoded

theorem functionTypeIndices_tail16_decoded :
    Internal.vectorLoop (Leb.u32) 92 { bytes := artifactBytes, pos := 1042, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item16_decoded functionTypeIndices_tail17_decoded

theorem functionTypeIndices_tail15_decoded :
    Internal.vectorLoop (Leb.u32) 93 { bytes := artifactBytes, pos := 1041, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item15_decoded functionTypeIndices_tail16_decoded

theorem functionTypeIndices_tail14_decoded :
    Internal.vectorLoop (Leb.u32) 94 { bytes := artifactBytes, pos := 1040, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item14_decoded functionTypeIndices_tail15_decoded

theorem functionTypeIndices_tail13_decoded :
    Internal.vectorLoop (Leb.u32) 95 { bytes := artifactBytes, pos := 1039, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item13_decoded functionTypeIndices_tail14_decoded

theorem functionTypeIndices_tail12_decoded :
    Internal.vectorLoop (Leb.u32) 96 { bytes := artifactBytes, pos := 1038, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item12_decoded functionTypeIndices_tail13_decoded

theorem functionTypeIndices_tail11_decoded :
    Internal.vectorLoop (Leb.u32) 97 { bytes := artifactBytes, pos := 1037, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item11_decoded functionTypeIndices_tail12_decoded

theorem functionTypeIndices_tail10_decoded :
    Internal.vectorLoop (Leb.u32) 98 { bytes := artifactBytes, pos := 1036, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item10_decoded functionTypeIndices_tail11_decoded

theorem functionTypeIndices_tail9_decoded :
    Internal.vectorLoop (Leb.u32) 99 { bytes := artifactBytes, pos := 1035, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item9_decoded functionTypeIndices_tail10_decoded

theorem functionTypeIndices_tail8_decoded :
    Internal.vectorLoop (Leb.u32) 100 { bytes := artifactBytes, pos := 1034, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item8_decoded functionTypeIndices_tail9_decoded

theorem functionTypeIndices_tail7_decoded :
    Internal.vectorLoop (Leb.u32) 101 { bytes := artifactBytes, pos := 1033, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item7_decoded functionTypeIndices_tail8_decoded

theorem functionTypeIndices_tail6_decoded :
    Internal.vectorLoop (Leb.u32) 102 { bytes := artifactBytes, pos := 1032, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item6_decoded functionTypeIndices_tail7_decoded

theorem functionTypeIndices_tail5_decoded :
    Internal.vectorLoop (Leb.u32) 103 { bytes := artifactBytes, pos := 1031, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item5_decoded functionTypeIndices_tail6_decoded

theorem functionTypeIndices_tail4_decoded :
    Internal.vectorLoop (Leb.u32) 104 { bytes := artifactBytes, pos := 1030, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item4_decoded functionTypeIndices_tail5_decoded

theorem functionTypeIndices_tail3_decoded :
    Internal.vectorLoop (Leb.u32) 105 { bytes := artifactBytes, pos := 1029, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item3_decoded functionTypeIndices_tail4_decoded

theorem functionTypeIndices_tail2_decoded :
    Internal.vectorLoop (Leb.u32) 106 { bytes := artifactBytes, pos := 1028, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item2_decoded functionTypeIndices_tail3_decoded

theorem functionTypeIndices_tail1_decoded :
    Internal.vectorLoop (Leb.u32) 107 { bytes := artifactBytes, pos := 1027, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item1_decoded functionTypeIndices_tail2_decoded

theorem functionTypeIndices_tail0_decoded :
    Internal.vectorLoop (Leb.u32) 108 { bytes := artifactBytes, pos := 1026, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item0_decoded functionTypeIndices_tail1_decoded

theorem functionTypeIndices_vector_decoded :
    vector (Leb.u32) { bytes := artifactBytes, pos := 1025, limit := 1134 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 1134, limit := 1134 }) := by
  refine vector_eq_of_parts (length := 108) (itemsStart := { bytes := artifactBytes, pos := 1026, limit := 1134 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0_decoded

#print axioms functionTypeIndices_vector_decoded

theorem memories_item0_decoded :
    memoryType { bytes := artifactBytes, pos := 1137, limit := 1139 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 1139, limit := 1139 }) := by
  cbv

theorem memories_tail1_decoded :
    Internal.vectorLoop (memoryType) 0 { bytes := artifactBytes, pos := 1139, limit := 1139 } =
      .ok (Cache.raw.memories.drop 1, { bytes := artifactBytes, pos := 1139, limit := 1139 }) := by rfl

theorem memories_tail0_decoded :
    Internal.vectorLoop (memoryType) 1 { bytes := artifactBytes, pos := 1137, limit := 1139 } =
      .ok (Cache.raw.memories.drop 0, { bytes := artifactBytes, pos := 1139, limit := 1139 }) := by
  exact vectorLoop_eq_cons memories_item0_decoded memories_tail1_decoded

theorem memories_vector_decoded :
    vector (memoryType) { bytes := artifactBytes, pos := 1136, limit := 1139 } =
      .ok (Cache.raw.memories, { bytes := artifactBytes, pos := 1139, limit := 1139 }) := by
  refine vector_eq_of_parts (length := 1) (itemsStart := { bytes := artifactBytes, pos := 1137, limit := 1139 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact memories_tail0_decoded

#print axioms memories_vector_decoded

theorem globals_item0_decoded :
    global { bytes := artifactBytes, pos := 1142, limit := 1173 } =
      .ok (Cache.raw.globals[0]!, { bytes := artifactBytes, pos := 1148, limit := 1173 }) := by
  cbv

theorem globals_item1_decoded :
    global { bytes := artifactBytes, pos := 1148, limit := 1173 } =
      .ok (Cache.raw.globals[1]!, { bytes := artifactBytes, pos := 1153, limit := 1173 }) := by
  cbv

theorem globals_item2_decoded :
    global { bytes := artifactBytes, pos := 1153, limit := 1173 } =
      .ok (Cache.raw.globals[2]!, { bytes := artifactBytes, pos := 1158, limit := 1173 }) := by
  cbv

theorem globals_item3_decoded :
    global { bytes := artifactBytes, pos := 1158, limit := 1173 } =
      .ok (Cache.raw.globals[3]!, { bytes := artifactBytes, pos := 1163, limit := 1173 }) := by
  cbv

theorem globals_item4_decoded :
    global { bytes := artifactBytes, pos := 1163, limit := 1173 } =
      .ok (Cache.raw.globals[4]!, { bytes := artifactBytes, pos := 1168, limit := 1173 }) := by
  cbv

theorem globals_item5_decoded :
    global { bytes := artifactBytes, pos := 1168, limit := 1173 } =
      .ok (Cache.raw.globals[5]!, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  cbv

theorem globals_tail6_decoded :
    Internal.vectorLoop (global) 0 { bytes := artifactBytes, pos := 1173, limit := 1173 } =
      .ok (Cache.raw.globals.drop 6, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by rfl

theorem globals_tail5_decoded :
    Internal.vectorLoop (global) 1 { bytes := artifactBytes, pos := 1168, limit := 1173 } =
      .ok (Cache.raw.globals.drop 5, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item5_decoded globals_tail6_decoded

theorem globals_tail4_decoded :
    Internal.vectorLoop (global) 2 { bytes := artifactBytes, pos := 1163, limit := 1173 } =
      .ok (Cache.raw.globals.drop 4, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item4_decoded globals_tail5_decoded

theorem globals_tail3_decoded :
    Internal.vectorLoop (global) 3 { bytes := artifactBytes, pos := 1158, limit := 1173 } =
      .ok (Cache.raw.globals.drop 3, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item3_decoded globals_tail4_decoded

theorem globals_tail2_decoded :
    Internal.vectorLoop (global) 4 { bytes := artifactBytes, pos := 1153, limit := 1173 } =
      .ok (Cache.raw.globals.drop 2, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item2_decoded globals_tail3_decoded

theorem globals_tail1_decoded :
    Internal.vectorLoop (global) 5 { bytes := artifactBytes, pos := 1148, limit := 1173 } =
      .ok (Cache.raw.globals.drop 1, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item1_decoded globals_tail2_decoded

theorem globals_tail0_decoded :
    Internal.vectorLoop (global) 6 { bytes := artifactBytes, pos := 1142, limit := 1173 } =
      .ok (Cache.raw.globals.drop 0, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  exact vectorLoop_eq_cons globals_item0_decoded globals_tail1_decoded

theorem globals_vector_decoded :
    vector (global) { bytes := artifactBytes, pos := 1141, limit := 1173 } =
      .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 1173, limit := 1173 }) := by
  refine vector_eq_of_parts (length := 6) (itemsStart := { bytes := artifactBytes, pos := 1142, limit := 1173 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact globals_tail0_decoded

#print axioms globals_vector_decoded

end Project.EulerRiemann.Artifact
