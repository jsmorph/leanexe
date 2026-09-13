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

theorem types_item0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 1023 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 16, limit := 1023 }) := by
  cbv

theorem types_item1_decoded :
    funcType { bytes := artifactBytes, pos := 16, limit := 1023 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 30, limit := 1023 }) := by
  cbv

theorem types_item2_decoded :
    funcType { bytes := artifactBytes, pos := 30, limit := 1023 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 35, limit := 1023 }) := by
  cbv

theorem types_item3_decoded :
    funcType { bytes := artifactBytes, pos := 35, limit := 1023 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 40, limit := 1023 }) := by
  cbv

theorem types_item4_decoded :
    funcType { bytes := artifactBytes, pos := 40, limit := 1023 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 45, limit := 1023 }) := by
  cbv

theorem types_item5_decoded :
    funcType { bytes := artifactBytes, pos := 45, limit := 1023 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 53, limit := 1023 }) := by
  cbv

theorem types_item6_decoded :
    funcType { bytes := artifactBytes, pos := 53, limit := 1023 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 58, limit := 1023 }) := by
  cbv

theorem types_item7_decoded :
    funcType { bytes := artifactBytes, pos := 58, limit := 1023 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 63, limit := 1023 }) := by
  cbv

theorem types_item8_decoded :
    funcType { bytes := artifactBytes, pos := 63, limit := 1023 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 68, limit := 1023 }) := by
  cbv

theorem types_item9_decoded :
    funcType { bytes := artifactBytes, pos := 68, limit := 1023 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 74, limit := 1023 }) := by
  cbv

theorem types_item10_decoded :
    funcType { bytes := artifactBytes, pos := 74, limit := 1023 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 79, limit := 1023 }) := by
  cbv

theorem types_item11_decoded :
    funcType { bytes := artifactBytes, pos := 79, limit := 1023 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 87, limit := 1023 }) := by
  cbv

theorem types_item12_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 1023 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 93, limit := 1023 }) := by
  cbv

theorem types_item13_decoded :
    funcType { bytes := artifactBytes, pos := 93, limit := 1023 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 99, limit := 1023 }) := by
  cbv

theorem types_item14_decoded :
    funcType { bytes := artifactBytes, pos := 99, limit := 1023 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 105, limit := 1023 }) := by
  cbv

theorem types_item15_decoded :
    funcType { bytes := artifactBytes, pos := 105, limit := 1023 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 113, limit := 1023 }) := by
  cbv

theorem types_item16_decoded :
    funcType { bytes := artifactBytes, pos := 113, limit := 1023 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 119, limit := 1023 }) := by
  cbv

theorem types_item17_decoded :
    funcType { bytes := artifactBytes, pos := 119, limit := 1023 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 125, limit := 1023 }) := by
  cbv

theorem types_item18_decoded :
    funcType { bytes := artifactBytes, pos := 125, limit := 1023 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 133, limit := 1023 }) := by
  cbv

theorem types_item19_decoded :
    funcType { bytes := artifactBytes, pos := 133, limit := 1023 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 141, limit := 1023 }) := by
  cbv

theorem types_item20_decoded :
    funcType { bytes := artifactBytes, pos := 141, limit := 1023 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 149, limit := 1023 }) := by
  cbv

theorem types_item21_decoded :
    funcType { bytes := artifactBytes, pos := 149, limit := 1023 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 160, limit := 1023 }) := by
  cbv

theorem types_item22_decoded :
    funcType { bytes := artifactBytes, pos := 160, limit := 1023 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 175, limit := 1023 }) := by
  cbv

theorem types_item23_decoded :
    funcType { bytes := artifactBytes, pos := 175, limit := 1023 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 183, limit := 1023 }) := by
  cbv

theorem types_item24_decoded :
    funcType { bytes := artifactBytes, pos := 183, limit := 1023 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 191, limit := 1023 }) := by
  cbv

theorem types_item25_decoded :
    funcType { bytes := artifactBytes, pos := 191, limit := 1023 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 199, limit := 1023 }) := by
  cbv

theorem types_item26_decoded :
    funcType { bytes := artifactBytes, pos := 199, limit := 1023 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 207, limit := 1023 }) := by
  cbv

theorem types_item27_decoded :
    funcType { bytes := artifactBytes, pos := 207, limit := 1023 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 213, limit := 1023 }) := by
  cbv

theorem types_item28_decoded :
    funcType { bytes := artifactBytes, pos := 213, limit := 1023 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 225, limit := 1023 }) := by
  cbv

theorem types_item29_decoded :
    funcType { bytes := artifactBytes, pos := 225, limit := 1023 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 231, limit := 1023 }) := by
  cbv

theorem types_item30_decoded :
    funcType { bytes := artifactBytes, pos := 231, limit := 1023 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 243, limit := 1023 }) := by
  cbv

theorem types_item31_decoded :
    funcType { bytes := artifactBytes, pos := 243, limit := 1023 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 257, limit := 1023 }) := by
  cbv

theorem types_item32_decoded :
    funcType { bytes := artifactBytes, pos := 257, limit := 1023 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 264, limit := 1023 }) := by
  cbv

theorem types_item33_decoded :
    funcType { bytes := artifactBytes, pos := 264, limit := 1023 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 269, limit := 1023 }) := by
  cbv

theorem types_item34_decoded :
    funcType { bytes := artifactBytes, pos := 269, limit := 1023 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 274, limit := 1023 }) := by
  cbv

theorem types_item35_decoded :
    funcType { bytes := artifactBytes, pos := 274, limit := 1023 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 281, limit := 1023 }) := by
  cbv

theorem types_item36_decoded :
    funcType { bytes := artifactBytes, pos := 281, limit := 1023 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 287, limit := 1023 }) := by
  cbv

theorem types_item37_decoded :
    funcType { bytes := artifactBytes, pos := 287, limit := 1023 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 295, limit := 1023 }) := by
  cbv

theorem types_item38_decoded :
    funcType { bytes := artifactBytes, pos := 295, limit := 1023 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 306, limit := 1023 }) := by
  cbv

theorem types_item39_decoded :
    funcType { bytes := artifactBytes, pos := 306, limit := 1023 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 318, limit := 1023 }) := by
  cbv

theorem types_item40_decoded :
    funcType { bytes := artifactBytes, pos := 318, limit := 1023 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 344, limit := 1023 }) := by
  cbv

theorem types_item41_decoded :
    funcType { bytes := artifactBytes, pos := 344, limit := 1023 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 349, limit := 1023 }) := by
  cbv

theorem types_item42_decoded :
    funcType { bytes := artifactBytes, pos := 349, limit := 1023 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 354, limit := 1023 }) := by
  cbv

theorem types_item43_decoded :
    funcType { bytes := artifactBytes, pos := 354, limit := 1023 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 359, limit := 1023 }) := by
  cbv

theorem types_item44_decoded :
    funcType { bytes := artifactBytes, pos := 359, limit := 1023 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 364, limit := 1023 }) := by
  cbv

theorem types_item45_decoded :
    funcType { bytes := artifactBytes, pos := 364, limit := 1023 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 374, limit := 1023 }) := by
  cbv

theorem types_item46_decoded :
    funcType { bytes := artifactBytes, pos := 374, limit := 1023 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 384, limit := 1023 }) := by
  cbv

theorem types_item47_decoded :
    funcType { bytes := artifactBytes, pos := 384, limit := 1023 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 396, limit := 1023 }) := by
  cbv

theorem types_item48_decoded :
    funcType { bytes := artifactBytes, pos := 396, limit := 1023 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 408, limit := 1023 }) := by
  cbv

theorem types_item49_decoded :
    funcType { bytes := artifactBytes, pos := 408, limit := 1023 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 420, limit := 1023 }) := by
  cbv

theorem types_item50_decoded :
    funcType { bytes := artifactBytes, pos := 420, limit := 1023 } =
      .ok (Cache.raw.types[50]!, { bytes := artifactBytes, pos := 432, limit := 1023 }) := by
  cbv

theorem types_item51_decoded :
    funcType { bytes := artifactBytes, pos := 432, limit := 1023 } =
      .ok (Cache.raw.types[51]!, { bytes := artifactBytes, pos := 438, limit := 1023 }) := by
  cbv

theorem types_item52_decoded :
    funcType { bytes := artifactBytes, pos := 438, limit := 1023 } =
      .ok (Cache.raw.types[52]!, { bytes := artifactBytes, pos := 444, limit := 1023 }) := by
  cbv

theorem types_item53_decoded :
    funcType { bytes := artifactBytes, pos := 444, limit := 1023 } =
      .ok (Cache.raw.types[53]!, { bytes := artifactBytes, pos := 453, limit := 1023 }) := by
  cbv

theorem types_item54_decoded :
    funcType { bytes := artifactBytes, pos := 453, limit := 1023 } =
      .ok (Cache.raw.types[54]!, { bytes := artifactBytes, pos := 470, limit := 1023 }) := by
  cbv

theorem types_item55_decoded :
    funcType { bytes := artifactBytes, pos := 470, limit := 1023 } =
      .ok (Cache.raw.types[55]!, { bytes := artifactBytes, pos := 480, limit := 1023 }) := by
  cbv

theorem types_item56_decoded :
    funcType { bytes := artifactBytes, pos := 480, limit := 1023 } =
      .ok (Cache.raw.types[56]!, { bytes := artifactBytes, pos := 490, limit := 1023 }) := by
  cbv

theorem types_item57_decoded :
    funcType { bytes := artifactBytes, pos := 490, limit := 1023 } =
      .ok (Cache.raw.types[57]!, { bytes := artifactBytes, pos := 499, limit := 1023 }) := by
  cbv

theorem types_item58_decoded :
    funcType { bytes := artifactBytes, pos := 499, limit := 1023 } =
      .ok (Cache.raw.types[58]!, { bytes := artifactBytes, pos := 508, limit := 1023 }) := by
  cbv

theorem types_item59_decoded :
    funcType { bytes := artifactBytes, pos := 508, limit := 1023 } =
      .ok (Cache.raw.types[59]!, { bytes := artifactBytes, pos := 518, limit := 1023 }) := by
  cbv

theorem types_item60_decoded :
    funcType { bytes := artifactBytes, pos := 518, limit := 1023 } =
      .ok (Cache.raw.types[60]!, { bytes := artifactBytes, pos := 528, limit := 1023 }) := by
  cbv

theorem types_item61_decoded :
    funcType { bytes := artifactBytes, pos := 528, limit := 1023 } =
      .ok (Cache.raw.types[61]!, { bytes := artifactBytes, pos := 538, limit := 1023 }) := by
  cbv

theorem types_item62_decoded :
    funcType { bytes := artifactBytes, pos := 538, limit := 1023 } =
      .ok (Cache.raw.types[62]!, { bytes := artifactBytes, pos := 548, limit := 1023 }) := by
  cbv

theorem types_item63_decoded :
    funcType { bytes := artifactBytes, pos := 548, limit := 1023 } =
      .ok (Cache.raw.types[63]!, { bytes := artifactBytes, pos := 560, limit := 1023 }) := by
  cbv

theorem types_item64_decoded :
    funcType { bytes := artifactBytes, pos := 560, limit := 1023 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 571, limit := 1023 }) := by
  cbv

theorem types_item65_decoded :
    funcType { bytes := artifactBytes, pos := 571, limit := 1023 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 595, limit := 1023 }) := by
  cbv

theorem types_item66_decoded :
    funcType { bytes := artifactBytes, pos := 595, limit := 1023 } =
      .ok (Cache.raw.types[66]!, { bytes := artifactBytes, pos := 614, limit := 1023 }) := by
  cbv

theorem types_item67_decoded :
    funcType { bytes := artifactBytes, pos := 614, limit := 1023 } =
      .ok (Cache.raw.types[67]!, { bytes := artifactBytes, pos := 633, limit := 1023 }) := by
  cbv

theorem types_item68_decoded :
    funcType { bytes := artifactBytes, pos := 633, limit := 1023 } =
      .ok (Cache.raw.types[68]!, { bytes := artifactBytes, pos := 652, limit := 1023 }) := by
  cbv

theorem types_item69_decoded :
    funcType { bytes := artifactBytes, pos := 652, limit := 1023 } =
      .ok (Cache.raw.types[69]!, { bytes := artifactBytes, pos := 676, limit := 1023 }) := by
  cbv

theorem types_item70_decoded :
    funcType { bytes := artifactBytes, pos := 676, limit := 1023 } =
      .ok (Cache.raw.types[70]!, { bytes := artifactBytes, pos := 688, limit := 1023 }) := by
  cbv

theorem types_item71_decoded :
    funcType { bytes := artifactBytes, pos := 688, limit := 1023 } =
      .ok (Cache.raw.types[71]!, { bytes := artifactBytes, pos := 700, limit := 1023 }) := by
  cbv

theorem types_item72_decoded :
    funcType { bytes := artifactBytes, pos := 700, limit := 1023 } =
      .ok (Cache.raw.types[72]!, { bytes := artifactBytes, pos := 712, limit := 1023 }) := by
  cbv

theorem types_item73_decoded :
    funcType { bytes := artifactBytes, pos := 712, limit := 1023 } =
      .ok (Cache.raw.types[73]!, { bytes := artifactBytes, pos := 724, limit := 1023 }) := by
  cbv

theorem types_item74_decoded :
    funcType { bytes := artifactBytes, pos := 724, limit := 1023 } =
      .ok (Cache.raw.types[74]!, { bytes := artifactBytes, pos := 736, limit := 1023 }) := by
  cbv

theorem types_item75_decoded :
    funcType { bytes := artifactBytes, pos := 736, limit := 1023 } =
      .ok (Cache.raw.types[75]!, { bytes := artifactBytes, pos := 748, limit := 1023 }) := by
  cbv

theorem types_item76_decoded :
    funcType { bytes := artifactBytes, pos := 748, limit := 1023 } =
      .ok (Cache.raw.types[76]!, { bytes := artifactBytes, pos := 770, limit := 1023 }) := by
  cbv

theorem types_item77_decoded :
    funcType { bytes := artifactBytes, pos := 770, limit := 1023 } =
      .ok (Cache.raw.types[77]!, { bytes := artifactBytes, pos := 780, limit := 1023 }) := by
  cbv

theorem types_item78_decoded :
    funcType { bytes := artifactBytes, pos := 780, limit := 1023 } =
      .ok (Cache.raw.types[78]!, { bytes := artifactBytes, pos := 791, limit := 1023 }) := by
  cbv

theorem types_item79_decoded :
    funcType { bytes := artifactBytes, pos := 791, limit := 1023 } =
      .ok (Cache.raw.types[79]!, { bytes := artifactBytes, pos := 797, limit := 1023 }) := by
  cbv

theorem types_item80_decoded :
    funcType { bytes := artifactBytes, pos := 797, limit := 1023 } =
      .ok (Cache.raw.types[80]!, { bytes := artifactBytes, pos := 806, limit := 1023 }) := by
  cbv

theorem types_item81_decoded :
    funcType { bytes := artifactBytes, pos := 806, limit := 1023 } =
      .ok (Cache.raw.types[81]!, { bytes := artifactBytes, pos := 819, limit := 1023 }) := by
  cbv

theorem types_item82_decoded :
    funcType { bytes := artifactBytes, pos := 819, limit := 1023 } =
      .ok (Cache.raw.types[82]!, { bytes := artifactBytes, pos := 827, limit := 1023 }) := by
  cbv

theorem types_item83_decoded :
    funcType { bytes := artifactBytes, pos := 827, limit := 1023 } =
      .ok (Cache.raw.types[83]!, { bytes := artifactBytes, pos := 835, limit := 1023 }) := by
  cbv

theorem types_item84_decoded :
    funcType { bytes := artifactBytes, pos := 835, limit := 1023 } =
      .ok (Cache.raw.types[84]!, { bytes := artifactBytes, pos := 844, limit := 1023 }) := by
  cbv

theorem types_item85_decoded :
    funcType { bytes := artifactBytes, pos := 844, limit := 1023 } =
      .ok (Cache.raw.types[85]!, { bytes := artifactBytes, pos := 856, limit := 1023 }) := by
  cbv

theorem types_item86_decoded :
    funcType { bytes := artifactBytes, pos := 856, limit := 1023 } =
      .ok (Cache.raw.types[86]!, { bytes := artifactBytes, pos := 861, limit := 1023 }) := by
  cbv

theorem types_item87_decoded :
    funcType { bytes := artifactBytes, pos := 861, limit := 1023 } =
      .ok (Cache.raw.types[87]!, { bytes := artifactBytes, pos := 871, limit := 1023 }) := by
  cbv

theorem types_item88_decoded :
    funcType { bytes := artifactBytes, pos := 871, limit := 1023 } =
      .ok (Cache.raw.types[88]!, { bytes := artifactBytes, pos := 882, limit := 1023 }) := by
  cbv

theorem types_item89_decoded :
    funcType { bytes := artifactBytes, pos := 882, limit := 1023 } =
      .ok (Cache.raw.types[89]!, { bytes := artifactBytes, pos := 889, limit := 1023 }) := by
  cbv

theorem types_item90_decoded :
    funcType { bytes := artifactBytes, pos := 889, limit := 1023 } =
      .ok (Cache.raw.types[90]!, { bytes := artifactBytes, pos := 896, limit := 1023 }) := by
  cbv

theorem types_item91_decoded :
    funcType { bytes := artifactBytes, pos := 896, limit := 1023 } =
      .ok (Cache.raw.types[91]!, { bytes := artifactBytes, pos := 903, limit := 1023 }) := by
  cbv

theorem types_item92_decoded :
    funcType { bytes := artifactBytes, pos := 903, limit := 1023 } =
      .ok (Cache.raw.types[92]!, { bytes := artifactBytes, pos := 910, limit := 1023 }) := by
  cbv

theorem types_item93_decoded :
    funcType { bytes := artifactBytes, pos := 910, limit := 1023 } =
      .ok (Cache.raw.types[93]!, { bytes := artifactBytes, pos := 919, limit := 1023 }) := by
  cbv

theorem types_item94_decoded :
    funcType { bytes := artifactBytes, pos := 919, limit := 1023 } =
      .ok (Cache.raw.types[94]!, { bytes := artifactBytes, pos := 931, limit := 1023 }) := by
  cbv

theorem types_item95_decoded :
    funcType { bytes := artifactBytes, pos := 931, limit := 1023 } =
      .ok (Cache.raw.types[95]!, { bytes := artifactBytes, pos := 941, limit := 1023 }) := by
  cbv

theorem types_item96_decoded :
    funcType { bytes := artifactBytes, pos := 941, limit := 1023 } =
      .ok (Cache.raw.types[96]!, { bytes := artifactBytes, pos := 947, limit := 1023 }) := by
  cbv

theorem types_item97_decoded :
    funcType { bytes := artifactBytes, pos := 947, limit := 1023 } =
      .ok (Cache.raw.types[97]!, { bytes := artifactBytes, pos := 955, limit := 1023 }) := by
  cbv

theorem types_item98_decoded :
    funcType { bytes := artifactBytes, pos := 955, limit := 1023 } =
      .ok (Cache.raw.types[98]!, { bytes := artifactBytes, pos := 966, limit := 1023 }) := by
  cbv

theorem types_item99_decoded :
    funcType { bytes := artifactBytes, pos := 966, limit := 1023 } =
      .ok (Cache.raw.types[99]!, { bytes := artifactBytes, pos := 976, limit := 1023 }) := by
  cbv

theorem types_item100_decoded :
    funcType { bytes := artifactBytes, pos := 976, limit := 1023 } =
      .ok (Cache.raw.types[100]!, { bytes := artifactBytes, pos := 984, limit := 1023 }) := by
  cbv

theorem types_item101_decoded :
    funcType { bytes := artifactBytes, pos := 984, limit := 1023 } =
      .ok (Cache.raw.types[101]!, { bytes := artifactBytes, pos := 992, limit := 1023 }) := by
  cbv

theorem types_item102_decoded :
    funcType { bytes := artifactBytes, pos := 992, limit := 1023 } =
      .ok (Cache.raw.types[102]!, { bytes := artifactBytes, pos := 1001, limit := 1023 }) := by
  cbv

theorem types_item103_decoded :
    funcType { bytes := artifactBytes, pos := 1001, limit := 1023 } =
      .ok (Cache.raw.types[103]!, { bytes := artifactBytes, pos := 1006, limit := 1023 }) := by
  cbv

theorem types_item104_decoded :
    funcType { bytes := artifactBytes, pos := 1006, limit := 1023 } =
      .ok (Cache.raw.types[104]!, { bytes := artifactBytes, pos := 1011, limit := 1023 }) := by
  cbv

theorem types_item105_decoded :
    funcType { bytes := artifactBytes, pos := 1011, limit := 1023 } =
      .ok (Cache.raw.types[105]!, { bytes := artifactBytes, pos := 1014, limit := 1023 }) := by
  cbv

theorem types_item106_decoded :
    funcType { bytes := artifactBytes, pos := 1014, limit := 1023 } =
      .ok (Cache.raw.types[106]!, { bytes := artifactBytes, pos := 1019, limit := 1023 }) := by
  cbv

theorem types_item107_decoded :
    funcType { bytes := artifactBytes, pos := 1019, limit := 1023 } =
      .ok (Cache.raw.types[107]!, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  cbv

theorem types_tail108_decoded :
    Internal.vectorLoop (funcType) 0 { bytes := artifactBytes, pos := 1023, limit := 1023 } =
      .ok (Cache.raw.types.drop 108, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by rfl

theorem types_tail107_decoded :
    Internal.vectorLoop (funcType) 1 { bytes := artifactBytes, pos := 1019, limit := 1023 } =
      .ok (Cache.raw.types.drop 107, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item107_decoded types_tail108_decoded

theorem types_tail106_decoded :
    Internal.vectorLoop (funcType) 2 { bytes := artifactBytes, pos := 1014, limit := 1023 } =
      .ok (Cache.raw.types.drop 106, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item106_decoded types_tail107_decoded

theorem types_tail105_decoded :
    Internal.vectorLoop (funcType) 3 { bytes := artifactBytes, pos := 1011, limit := 1023 } =
      .ok (Cache.raw.types.drop 105, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item105_decoded types_tail106_decoded

theorem types_tail104_decoded :
    Internal.vectorLoop (funcType) 4 { bytes := artifactBytes, pos := 1006, limit := 1023 } =
      .ok (Cache.raw.types.drop 104, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item104_decoded types_tail105_decoded

theorem types_tail103_decoded :
    Internal.vectorLoop (funcType) 5 { bytes := artifactBytes, pos := 1001, limit := 1023 } =
      .ok (Cache.raw.types.drop 103, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item103_decoded types_tail104_decoded

theorem types_tail102_decoded :
    Internal.vectorLoop (funcType) 6 { bytes := artifactBytes, pos := 992, limit := 1023 } =
      .ok (Cache.raw.types.drop 102, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item102_decoded types_tail103_decoded

theorem types_tail101_decoded :
    Internal.vectorLoop (funcType) 7 { bytes := artifactBytes, pos := 984, limit := 1023 } =
      .ok (Cache.raw.types.drop 101, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item101_decoded types_tail102_decoded

theorem types_tail100_decoded :
    Internal.vectorLoop (funcType) 8 { bytes := artifactBytes, pos := 976, limit := 1023 } =
      .ok (Cache.raw.types.drop 100, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item100_decoded types_tail101_decoded

theorem types_tail99_decoded :
    Internal.vectorLoop (funcType) 9 { bytes := artifactBytes, pos := 966, limit := 1023 } =
      .ok (Cache.raw.types.drop 99, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item99_decoded types_tail100_decoded

theorem types_tail98_decoded :
    Internal.vectorLoop (funcType) 10 { bytes := artifactBytes, pos := 955, limit := 1023 } =
      .ok (Cache.raw.types.drop 98, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item98_decoded types_tail99_decoded

theorem types_tail97_decoded :
    Internal.vectorLoop (funcType) 11 { bytes := artifactBytes, pos := 947, limit := 1023 } =
      .ok (Cache.raw.types.drop 97, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item97_decoded types_tail98_decoded

theorem types_tail96_decoded :
    Internal.vectorLoop (funcType) 12 { bytes := artifactBytes, pos := 941, limit := 1023 } =
      .ok (Cache.raw.types.drop 96, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item96_decoded types_tail97_decoded

theorem types_tail95_decoded :
    Internal.vectorLoop (funcType) 13 { bytes := artifactBytes, pos := 931, limit := 1023 } =
      .ok (Cache.raw.types.drop 95, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item95_decoded types_tail96_decoded

theorem types_tail94_decoded :
    Internal.vectorLoop (funcType) 14 { bytes := artifactBytes, pos := 919, limit := 1023 } =
      .ok (Cache.raw.types.drop 94, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item94_decoded types_tail95_decoded

theorem types_tail93_decoded :
    Internal.vectorLoop (funcType) 15 { bytes := artifactBytes, pos := 910, limit := 1023 } =
      .ok (Cache.raw.types.drop 93, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item93_decoded types_tail94_decoded

theorem types_tail92_decoded :
    Internal.vectorLoop (funcType) 16 { bytes := artifactBytes, pos := 903, limit := 1023 } =
      .ok (Cache.raw.types.drop 92, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item92_decoded types_tail93_decoded

theorem types_tail91_decoded :
    Internal.vectorLoop (funcType) 17 { bytes := artifactBytes, pos := 896, limit := 1023 } =
      .ok (Cache.raw.types.drop 91, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item91_decoded types_tail92_decoded

theorem types_tail90_decoded :
    Internal.vectorLoop (funcType) 18 { bytes := artifactBytes, pos := 889, limit := 1023 } =
      .ok (Cache.raw.types.drop 90, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item90_decoded types_tail91_decoded

theorem types_tail89_decoded :
    Internal.vectorLoop (funcType) 19 { bytes := artifactBytes, pos := 882, limit := 1023 } =
      .ok (Cache.raw.types.drop 89, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item89_decoded types_tail90_decoded

theorem types_tail88_decoded :
    Internal.vectorLoop (funcType) 20 { bytes := artifactBytes, pos := 871, limit := 1023 } =
      .ok (Cache.raw.types.drop 88, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item88_decoded types_tail89_decoded

theorem types_tail87_decoded :
    Internal.vectorLoop (funcType) 21 { bytes := artifactBytes, pos := 861, limit := 1023 } =
      .ok (Cache.raw.types.drop 87, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item87_decoded types_tail88_decoded

theorem types_tail86_decoded :
    Internal.vectorLoop (funcType) 22 { bytes := artifactBytes, pos := 856, limit := 1023 } =
      .ok (Cache.raw.types.drop 86, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item86_decoded types_tail87_decoded

theorem types_tail85_decoded :
    Internal.vectorLoop (funcType) 23 { bytes := artifactBytes, pos := 844, limit := 1023 } =
      .ok (Cache.raw.types.drop 85, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item85_decoded types_tail86_decoded

theorem types_tail84_decoded :
    Internal.vectorLoop (funcType) 24 { bytes := artifactBytes, pos := 835, limit := 1023 } =
      .ok (Cache.raw.types.drop 84, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item84_decoded types_tail85_decoded

theorem types_tail83_decoded :
    Internal.vectorLoop (funcType) 25 { bytes := artifactBytes, pos := 827, limit := 1023 } =
      .ok (Cache.raw.types.drop 83, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item83_decoded types_tail84_decoded

theorem types_tail82_decoded :
    Internal.vectorLoop (funcType) 26 { bytes := artifactBytes, pos := 819, limit := 1023 } =
      .ok (Cache.raw.types.drop 82, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item82_decoded types_tail83_decoded

theorem types_tail81_decoded :
    Internal.vectorLoop (funcType) 27 { bytes := artifactBytes, pos := 806, limit := 1023 } =
      .ok (Cache.raw.types.drop 81, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item81_decoded types_tail82_decoded

theorem types_tail80_decoded :
    Internal.vectorLoop (funcType) 28 { bytes := artifactBytes, pos := 797, limit := 1023 } =
      .ok (Cache.raw.types.drop 80, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item80_decoded types_tail81_decoded

theorem types_tail79_decoded :
    Internal.vectorLoop (funcType) 29 { bytes := artifactBytes, pos := 791, limit := 1023 } =
      .ok (Cache.raw.types.drop 79, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item79_decoded types_tail80_decoded

theorem types_tail78_decoded :
    Internal.vectorLoop (funcType) 30 { bytes := artifactBytes, pos := 780, limit := 1023 } =
      .ok (Cache.raw.types.drop 78, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item78_decoded types_tail79_decoded

theorem types_tail77_decoded :
    Internal.vectorLoop (funcType) 31 { bytes := artifactBytes, pos := 770, limit := 1023 } =
      .ok (Cache.raw.types.drop 77, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item77_decoded types_tail78_decoded

theorem types_tail76_decoded :
    Internal.vectorLoop (funcType) 32 { bytes := artifactBytes, pos := 748, limit := 1023 } =
      .ok (Cache.raw.types.drop 76, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item76_decoded types_tail77_decoded

theorem types_tail75_decoded :
    Internal.vectorLoop (funcType) 33 { bytes := artifactBytes, pos := 736, limit := 1023 } =
      .ok (Cache.raw.types.drop 75, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item75_decoded types_tail76_decoded

theorem types_tail74_decoded :
    Internal.vectorLoop (funcType) 34 { bytes := artifactBytes, pos := 724, limit := 1023 } =
      .ok (Cache.raw.types.drop 74, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item74_decoded types_tail75_decoded

theorem types_tail73_decoded :
    Internal.vectorLoop (funcType) 35 { bytes := artifactBytes, pos := 712, limit := 1023 } =
      .ok (Cache.raw.types.drop 73, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item73_decoded types_tail74_decoded

theorem types_tail72_decoded :
    Internal.vectorLoop (funcType) 36 { bytes := artifactBytes, pos := 700, limit := 1023 } =
      .ok (Cache.raw.types.drop 72, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item72_decoded types_tail73_decoded

theorem types_tail71_decoded :
    Internal.vectorLoop (funcType) 37 { bytes := artifactBytes, pos := 688, limit := 1023 } =
      .ok (Cache.raw.types.drop 71, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item71_decoded types_tail72_decoded

theorem types_tail70_decoded :
    Internal.vectorLoop (funcType) 38 { bytes := artifactBytes, pos := 676, limit := 1023 } =
      .ok (Cache.raw.types.drop 70, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item70_decoded types_tail71_decoded

theorem types_tail69_decoded :
    Internal.vectorLoop (funcType) 39 { bytes := artifactBytes, pos := 652, limit := 1023 } =
      .ok (Cache.raw.types.drop 69, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item69_decoded types_tail70_decoded

theorem types_tail68_decoded :
    Internal.vectorLoop (funcType) 40 { bytes := artifactBytes, pos := 633, limit := 1023 } =
      .ok (Cache.raw.types.drop 68, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item68_decoded types_tail69_decoded

theorem types_tail67_decoded :
    Internal.vectorLoop (funcType) 41 { bytes := artifactBytes, pos := 614, limit := 1023 } =
      .ok (Cache.raw.types.drop 67, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item67_decoded types_tail68_decoded

theorem types_tail66_decoded :
    Internal.vectorLoop (funcType) 42 { bytes := artifactBytes, pos := 595, limit := 1023 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item66_decoded types_tail67_decoded

theorem types_tail65_decoded :
    Internal.vectorLoop (funcType) 43 { bytes := artifactBytes, pos := 571, limit := 1023 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item65_decoded types_tail66_decoded

theorem types_tail64_decoded :
    Internal.vectorLoop (funcType) 44 { bytes := artifactBytes, pos := 560, limit := 1023 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item64_decoded types_tail65_decoded

theorem types_tail63_decoded :
    Internal.vectorLoop (funcType) 45 { bytes := artifactBytes, pos := 548, limit := 1023 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item63_decoded types_tail64_decoded

theorem types_tail62_decoded :
    Internal.vectorLoop (funcType) 46 { bytes := artifactBytes, pos := 538, limit := 1023 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item62_decoded types_tail63_decoded

theorem types_tail61_decoded :
    Internal.vectorLoop (funcType) 47 { bytes := artifactBytes, pos := 528, limit := 1023 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item61_decoded types_tail62_decoded

theorem types_tail60_decoded :
    Internal.vectorLoop (funcType) 48 { bytes := artifactBytes, pos := 518, limit := 1023 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item60_decoded types_tail61_decoded

theorem types_tail59_decoded :
    Internal.vectorLoop (funcType) 49 { bytes := artifactBytes, pos := 508, limit := 1023 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item59_decoded types_tail60_decoded

theorem types_tail58_decoded :
    Internal.vectorLoop (funcType) 50 { bytes := artifactBytes, pos := 499, limit := 1023 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item58_decoded types_tail59_decoded

theorem types_tail57_decoded :
    Internal.vectorLoop (funcType) 51 { bytes := artifactBytes, pos := 490, limit := 1023 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item57_decoded types_tail58_decoded

theorem types_tail56_decoded :
    Internal.vectorLoop (funcType) 52 { bytes := artifactBytes, pos := 480, limit := 1023 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item56_decoded types_tail57_decoded

theorem types_tail55_decoded :
    Internal.vectorLoop (funcType) 53 { bytes := artifactBytes, pos := 470, limit := 1023 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item55_decoded types_tail56_decoded

theorem types_tail54_decoded :
    Internal.vectorLoop (funcType) 54 { bytes := artifactBytes, pos := 453, limit := 1023 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item54_decoded types_tail55_decoded

theorem types_tail53_decoded :
    Internal.vectorLoop (funcType) 55 { bytes := artifactBytes, pos := 444, limit := 1023 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item53_decoded types_tail54_decoded

theorem types_tail52_decoded :
    Internal.vectorLoop (funcType) 56 { bytes := artifactBytes, pos := 438, limit := 1023 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item52_decoded types_tail53_decoded

theorem types_tail51_decoded :
    Internal.vectorLoop (funcType) 57 { bytes := artifactBytes, pos := 432, limit := 1023 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item51_decoded types_tail52_decoded

theorem types_tail50_decoded :
    Internal.vectorLoop (funcType) 58 { bytes := artifactBytes, pos := 420, limit := 1023 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item50_decoded types_tail51_decoded

theorem types_tail49_decoded :
    Internal.vectorLoop (funcType) 59 { bytes := artifactBytes, pos := 408, limit := 1023 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item49_decoded types_tail50_decoded

theorem types_tail48_decoded :
    Internal.vectorLoop (funcType) 60 { bytes := artifactBytes, pos := 396, limit := 1023 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item48_decoded types_tail49_decoded

theorem types_tail47_decoded :
    Internal.vectorLoop (funcType) 61 { bytes := artifactBytes, pos := 384, limit := 1023 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item47_decoded types_tail48_decoded

theorem types_tail46_decoded :
    Internal.vectorLoop (funcType) 62 { bytes := artifactBytes, pos := 374, limit := 1023 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item46_decoded types_tail47_decoded

theorem types_tail45_decoded :
    Internal.vectorLoop (funcType) 63 { bytes := artifactBytes, pos := 364, limit := 1023 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item45_decoded types_tail46_decoded

theorem types_tail44_decoded :
    Internal.vectorLoop (funcType) 64 { bytes := artifactBytes, pos := 359, limit := 1023 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop (funcType) 65 { bytes := artifactBytes, pos := 354, limit := 1023 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop (funcType) 66 { bytes := artifactBytes, pos := 349, limit := 1023 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop (funcType) 67 { bytes := artifactBytes, pos := 344, limit := 1023 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop (funcType) 68 { bytes := artifactBytes, pos := 318, limit := 1023 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop (funcType) 69 { bytes := artifactBytes, pos := 306, limit := 1023 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop (funcType) 70 { bytes := artifactBytes, pos := 295, limit := 1023 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop (funcType) 71 { bytes := artifactBytes, pos := 287, limit := 1023 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop (funcType) 72 { bytes := artifactBytes, pos := 281, limit := 1023 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item36_decoded types_tail37_decoded

theorem types_tail35_decoded :
    Internal.vectorLoop (funcType) 73 { bytes := artifactBytes, pos := 274, limit := 1023 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop (funcType) 74 { bytes := artifactBytes, pos := 269, limit := 1023 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop (funcType) 75 { bytes := artifactBytes, pos := 264, limit := 1023 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop (funcType) 76 { bytes := artifactBytes, pos := 257, limit := 1023 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop (funcType) 77 { bytes := artifactBytes, pos := 243, limit := 1023 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop (funcType) 78 { bytes := artifactBytes, pos := 231, limit := 1023 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop (funcType) 79 { bytes := artifactBytes, pos := 225, limit := 1023 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop (funcType) 80 { bytes := artifactBytes, pos := 213, limit := 1023 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop (funcType) 81 { bytes := artifactBytes, pos := 207, limit := 1023 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop (funcType) 82 { bytes := artifactBytes, pos := 199, limit := 1023 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop (funcType) 83 { bytes := artifactBytes, pos := 191, limit := 1023 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop (funcType) 84 { bytes := artifactBytes, pos := 183, limit := 1023 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop (funcType) 85 { bytes := artifactBytes, pos := 175, limit := 1023 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop (funcType) 86 { bytes := artifactBytes, pos := 160, limit := 1023 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop (funcType) 87 { bytes := artifactBytes, pos := 149, limit := 1023 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop (funcType) 88 { bytes := artifactBytes, pos := 141, limit := 1023 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item20_decoded types_tail21_decoded

theorem types_tail19_decoded :
    Internal.vectorLoop (funcType) 89 { bytes := artifactBytes, pos := 133, limit := 1023 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop (funcType) 90 { bytes := artifactBytes, pos := 125, limit := 1023 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop (funcType) 91 { bytes := artifactBytes, pos := 119, limit := 1023 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop (funcType) 92 { bytes := artifactBytes, pos := 113, limit := 1023 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop (funcType) 93 { bytes := artifactBytes, pos := 105, limit := 1023 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop (funcType) 94 { bytes := artifactBytes, pos := 99, limit := 1023 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop (funcType) 95 { bytes := artifactBytes, pos := 93, limit := 1023 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop (funcType) 96 { bytes := artifactBytes, pos := 87, limit := 1023 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop (funcType) 97 { bytes := artifactBytes, pos := 79, limit := 1023 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop (funcType) 98 { bytes := artifactBytes, pos := 74, limit := 1023 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop (funcType) 99 { bytes := artifactBytes, pos := 68, limit := 1023 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop (funcType) 100 { bytes := artifactBytes, pos := 63, limit := 1023 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop (funcType) 101 { bytes := artifactBytes, pos := 58, limit := 1023 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop (funcType) 102 { bytes := artifactBytes, pos := 53, limit := 1023 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop (funcType) 103 { bytes := artifactBytes, pos := 45, limit := 1023 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop (funcType) 104 { bytes := artifactBytes, pos := 40, limit := 1023 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop (funcType) 105 { bytes := artifactBytes, pos := 35, limit := 1023 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop (funcType) 106 { bytes := artifactBytes, pos := 30, limit := 1023 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop (funcType) 107 { bytes := artifactBytes, pos := 16, limit := 1023 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop (funcType) 108 { bytes := artifactBytes, pos := 12, limit := 1023 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  exact vectorLoop_eq_cons types_item0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector (funcType) { bytes := artifactBytes, pos := 11, limit := 1023 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 1023, limit := 1023 }) := by
  refine vector_eq_of_parts (length := 108) (itemsStart := { bytes := artifactBytes, pos := 12, limit := 1023 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded

end Project.EulerRiemann.Artifact
