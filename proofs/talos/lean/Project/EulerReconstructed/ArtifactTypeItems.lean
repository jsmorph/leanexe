import Project.EulerReconstructed.ArtifactTypeEntries0To31
import Project.EulerReconstructed.ArtifactTypeEntries32To63
import Project.EulerReconstructed.ArtifactTypeEntries64To95
import Project.EulerReconstructed.ArtifactTypeEntries96To127
import Project.EulerReconstructed.ArtifactTypeEntries128To152
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_tail153_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 1622, limit := 1622 } =
      .ok (Cache.raw.types.drop 153, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by rfl

theorem types_tail152_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 1618, limit := 1622 } =
      .ok (Cache.raw.types.drop 152, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type152_decoded types_tail153_decoded

theorem types_tail151_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 1613, limit := 1622 } =
      .ok (Cache.raw.types.drop 151, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type151_decoded types_tail152_decoded

theorem types_tail150_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 1610, limit := 1622 } =
      .ok (Cache.raw.types.drop 150, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type150_decoded types_tail151_decoded

theorem types_tail149_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 1605, limit := 1622 } =
      .ok (Cache.raw.types.drop 149, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type149_decoded types_tail150_decoded

theorem types_tail148_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 1599, limit := 1622 } =
      .ok (Cache.raw.types.drop 148, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type148_decoded types_tail149_decoded

theorem types_tail147_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 1590, limit := 1622 } =
      .ok (Cache.raw.types.drop 147, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type147_decoded types_tail148_decoded

theorem types_tail146_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 1582, limit := 1622 } =
      .ok (Cache.raw.types.drop 146, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type146_decoded types_tail147_decoded

theorem types_tail145_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 1574, limit := 1622 } =
      .ok (Cache.raw.types.drop 145, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type145_decoded types_tail146_decoded

theorem types_tail144_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 1564, limit := 1622 } =
      .ok (Cache.raw.types.drop 144, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type144_decoded types_tail145_decoded

theorem types_tail143_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 1553, limit := 1622 } =
      .ok (Cache.raw.types.drop 143, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type143_decoded types_tail144_decoded

theorem types_tail142_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 1544, limit := 1622 } =
      .ok (Cache.raw.types.drop 142, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type142_decoded types_tail143_decoded

theorem types_tail141_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 1538, limit := 1622 } =
      .ok (Cache.raw.types.drop 141, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type141_decoded types_tail142_decoded

theorem types_tail140_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 1528, limit := 1622 } =
      .ok (Cache.raw.types.drop 140, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type140_decoded types_tail141_decoded

theorem types_tail139_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 1516, limit := 1622 } =
      .ok (Cache.raw.types.drop 139, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type139_decoded types_tail140_decoded

theorem types_tail138_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 1501, limit := 1622 } =
      .ok (Cache.raw.types.drop 138, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type138_decoded types_tail139_decoded

theorem types_tail137_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 1492, limit := 1622 } =
      .ok (Cache.raw.types.drop 137, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type137_decoded types_tail138_decoded

theorem types_tail136_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 1485, limit := 1622 } =
      .ok (Cache.raw.types.drop 136, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type136_decoded types_tail137_decoded

theorem types_tail135_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 1478, limit := 1622 } =
      .ok (Cache.raw.types.drop 135, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type135_decoded types_tail136_decoded

theorem types_tail134_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 1471, limit := 1622 } =
      .ok (Cache.raw.types.drop 134, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type134_decoded types_tail135_decoded

theorem types_tail133_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 1464, limit := 1622 } =
      .ok (Cache.raw.types.drop 133, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type133_decoded types_tail134_decoded

theorem types_tail132_decoded :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 1453, limit := 1622 } =
      .ok (Cache.raw.types.drop 132, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type132_decoded types_tail133_decoded

theorem types_tail131_decoded :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 1443, limit := 1622 } =
      .ok (Cache.raw.types.drop 131, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type131_decoded types_tail132_decoded

theorem types_tail130_decoded :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 1438, limit := 1622 } =
      .ok (Cache.raw.types.drop 130, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type130_decoded types_tail131_decoded

theorem types_tail129_decoded :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 1425, limit := 1622 } =
      .ok (Cache.raw.types.drop 129, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type129_decoded types_tail130_decoded

theorem types_tail128_decoded :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 1416, limit := 1622 } =
      .ok (Cache.raw.types.drop 128, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type128_decoded types_tail129_decoded

theorem types_tail127_decoded :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 1408, limit := 1622 } =
      .ok (Cache.raw.types.drop 127, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type127_decoded types_tail128_decoded

theorem types_tail126_decoded :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 1400, limit := 1622 } =
      .ok (Cache.raw.types.drop 126, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type126_decoded types_tail127_decoded

theorem types_tail125_decoded :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 1385, limit := 1622 } =
      .ok (Cache.raw.types.drop 125, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type125_decoded types_tail126_decoded

theorem types_tail124_decoded :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 1375, limit := 1622 } =
      .ok (Cache.raw.types.drop 124, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type124_decoded types_tail125_decoded

theorem types_tail123_decoded :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 1369, limit := 1622 } =
      .ok (Cache.raw.types.drop 123, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type123_decoded types_tail124_decoded

theorem types_tail122_decoded :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 1358, limit := 1622 } =
      .ok (Cache.raw.types.drop 122, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type122_decoded types_tail123_decoded

theorem types_tail121_decoded :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 1347, limit := 1622 } =
      .ok (Cache.raw.types.drop 121, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type121_decoded types_tail122_decoded

theorem types_tail120_decoded :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 1324, limit := 1622 } =
      .ok (Cache.raw.types.drop 120, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type120_decoded types_tail121_decoded

theorem types_tail119_decoded :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 1312, limit := 1622 } =
      .ok (Cache.raw.types.drop 119, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type119_decoded types_tail120_decoded

theorem types_tail118_decoded :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 1300, limit := 1622 } =
      .ok (Cache.raw.types.drop 118, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type118_decoded types_tail119_decoded

theorem types_tail117_decoded :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 1288, limit := 1622 } =
      .ok (Cache.raw.types.drop 117, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type117_decoded types_tail118_decoded

theorem types_tail116_decoded :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 1276, limit := 1622 } =
      .ok (Cache.raw.types.drop 116, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type116_decoded types_tail117_decoded

theorem types_tail115_decoded :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 1264, limit := 1622 } =
      .ok (Cache.raw.types.drop 115, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type115_decoded types_tail116_decoded

theorem types_tail114_decoded :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 1252, limit := 1622 } =
      .ok (Cache.raw.types.drop 114, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type114_decoded types_tail115_decoded

theorem types_tail113_decoded :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 1225, limit := 1622 } =
      .ok (Cache.raw.types.drop 113, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type113_decoded types_tail114_decoded

theorem types_tail112_decoded :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 1198, limit := 1622 } =
      .ok (Cache.raw.types.drop 112, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type112_decoded types_tail113_decoded

theorem types_tail111_decoded :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 1171, limit := 1622 } =
      .ok (Cache.raw.types.drop 111, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type111_decoded types_tail112_decoded

theorem types_tail110_decoded :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 1144, limit := 1622 } =
      .ok (Cache.raw.types.drop 110, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type110_decoded types_tail111_decoded

theorem types_tail109_decoded :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 1117, limit := 1622 } =
      .ok (Cache.raw.types.drop 109, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type109_decoded types_tail110_decoded

theorem types_tail108_decoded :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 1084, limit := 1622 } =
      .ok (Cache.raw.types.drop 108, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type108_decoded types_tail109_decoded

theorem types_tail107_decoded :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 1067, limit := 1622 } =
      .ok (Cache.raw.types.drop 107, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type107_decoded types_tail108_decoded

theorem types_tail106_decoded :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 1050, limit := 1622 } =
      .ok (Cache.raw.types.drop 106, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type106_decoded types_tail107_decoded

theorem types_tail105_decoded :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 1018, limit := 1622 } =
      .ok (Cache.raw.types.drop 105, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type105_decoded types_tail106_decoded

theorem types_tail104_decoded :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 990, limit := 1622 } =
      .ok (Cache.raw.types.drop 104, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type104_decoded types_tail105_decoded

theorem types_tail103_decoded :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 979, limit := 1622 } =
      .ok (Cache.raw.types.drop 103, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type103_decoded types_tail104_decoded

theorem types_tail102_decoded :
    Internal.vectorLoop funcType 51 { bytes := artifactBytes, pos := 967, limit := 1622 } =
      .ok (Cache.raw.types.drop 102, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type102_decoded types_tail103_decoded

theorem types_tail101_decoded :
    Internal.vectorLoop funcType 52 { bytes := artifactBytes, pos := 957, limit := 1622 } =
      .ok (Cache.raw.types.drop 101, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type101_decoded types_tail102_decoded

theorem types_tail100_decoded :
    Internal.vectorLoop funcType 53 { bytes := artifactBytes, pos := 947, limit := 1622 } =
      .ok (Cache.raw.types.drop 100, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type100_decoded types_tail101_decoded

theorem types_tail99_decoded :
    Internal.vectorLoop funcType 54 { bytes := artifactBytes, pos := 937, limit := 1622 } =
      .ok (Cache.raw.types.drop 99, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type99_decoded types_tail100_decoded

theorem types_tail98_decoded :
    Internal.vectorLoop funcType 55 { bytes := artifactBytes, pos := 927, limit := 1622 } =
      .ok (Cache.raw.types.drop 98, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type98_decoded types_tail99_decoded

theorem types_tail97_decoded :
    Internal.vectorLoop funcType 56 { bytes := artifactBytes, pos := 918, limit := 1622 } =
      .ok (Cache.raw.types.drop 97, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type97_decoded types_tail98_decoded

theorem types_tail96_decoded :
    Internal.vectorLoop funcType 57 { bytes := artifactBytes, pos := 909, limit := 1622 } =
      .ok (Cache.raw.types.drop 96, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type96_decoded types_tail97_decoded

theorem types_tail95_decoded :
    Internal.vectorLoop funcType 58 { bytes := artifactBytes, pos := 899, limit := 1622 } =
      .ok (Cache.raw.types.drop 95, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type95_decoded types_tail96_decoded

theorem types_tail94_decoded :
    Internal.vectorLoop funcType 59 { bytes := artifactBytes, pos := 889, limit := 1622 } =
      .ok (Cache.raw.types.drop 94, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type94_decoded types_tail95_decoded

theorem types_tail93_decoded :
    Internal.vectorLoop funcType 60 { bytes := artifactBytes, pos := 872, limit := 1622 } =
      .ok (Cache.raw.types.drop 93, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type93_decoded types_tail94_decoded

theorem types_tail92_decoded :
    Internal.vectorLoop funcType 61 { bytes := artifactBytes, pos := 863, limit := 1622 } =
      .ok (Cache.raw.types.drop 92, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type92_decoded types_tail93_decoded

theorem types_tail91_decoded :
    Internal.vectorLoop funcType 62 { bytes := artifactBytes, pos := 857, limit := 1622 } =
      .ok (Cache.raw.types.drop 91, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type91_decoded types_tail92_decoded

theorem types_tail90_decoded :
    Internal.vectorLoop funcType 63 { bytes := artifactBytes, pos := 851, limit := 1622 } =
      .ok (Cache.raw.types.drop 90, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type90_decoded types_tail91_decoded

theorem types_tail89_decoded :
    Internal.vectorLoop funcType 64 { bytes := artifactBytes, pos := 839, limit := 1622 } =
      .ok (Cache.raw.types.drop 89, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type89_decoded types_tail90_decoded

theorem types_tail88_decoded :
    Internal.vectorLoop funcType 65 { bytes := artifactBytes, pos := 827, limit := 1622 } =
      .ok (Cache.raw.types.drop 88, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type88_decoded types_tail89_decoded

theorem types_tail87_decoded :
    Internal.vectorLoop funcType 66 { bytes := artifactBytes, pos := 815, limit := 1622 } =
      .ok (Cache.raw.types.drop 87, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type87_decoded types_tail88_decoded

theorem types_tail86_decoded :
    Internal.vectorLoop funcType 67 { bytes := artifactBytes, pos := 803, limit := 1622 } =
      .ok (Cache.raw.types.drop 86, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type86_decoded types_tail87_decoded

theorem types_tail85_decoded :
    Internal.vectorLoop funcType 68 { bytes := artifactBytes, pos := 793, limit := 1622 } =
      .ok (Cache.raw.types.drop 85, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type85_decoded types_tail86_decoded

theorem types_tail84_decoded :
    Internal.vectorLoop funcType 69 { bytes := artifactBytes, pos := 783, limit := 1622 } =
      .ok (Cache.raw.types.drop 84, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type84_decoded types_tail85_decoded

theorem types_tail83_decoded :
    Internal.vectorLoop funcType 70 { bytes := artifactBytes, pos := 778, limit := 1622 } =
      .ok (Cache.raw.types.drop 83, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type83_decoded types_tail84_decoded

theorem types_tail82_decoded :
    Internal.vectorLoop funcType 71 { bytes := artifactBytes, pos := 773, limit := 1622 } =
      .ok (Cache.raw.types.drop 82, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type82_decoded types_tail83_decoded

theorem types_tail81_decoded :
    Internal.vectorLoop funcType 72 { bytes := artifactBytes, pos := 768, limit := 1622 } =
      .ok (Cache.raw.types.drop 81, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type81_decoded types_tail82_decoded

theorem types_tail80_decoded :
    Internal.vectorLoop funcType 73 { bytes := artifactBytes, pos := 763, limit := 1622 } =
      .ok (Cache.raw.types.drop 80, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type80_decoded types_tail81_decoded

theorem types_tail79_decoded :
    Internal.vectorLoop funcType 74 { bytes := artifactBytes, pos := 751, limit := 1622 } =
      .ok (Cache.raw.types.drop 79, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type79_decoded types_tail80_decoded

theorem types_tail78_decoded :
    Internal.vectorLoop funcType 75 { bytes := artifactBytes, pos := 739, limit := 1622 } =
      .ok (Cache.raw.types.drop 78, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type78_decoded types_tail79_decoded

theorem types_tail77_decoded :
    Internal.vectorLoop funcType 76 { bytes := artifactBytes, pos := 724, limit := 1622 } =
      .ok (Cache.raw.types.drop 77, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type77_decoded types_tail78_decoded

theorem types_tail76_decoded :
    Internal.vectorLoop funcType 77 { bytes := artifactBytes, pos := 713, limit := 1622 } =
      .ok (Cache.raw.types.drop 76, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type76_decoded types_tail77_decoded

theorem types_tail75_decoded :
    Internal.vectorLoop funcType 78 { bytes := artifactBytes, pos := 687, limit := 1622 } =
      .ok (Cache.raw.types.drop 75, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type75_decoded types_tail76_decoded

theorem types_tail74_decoded :
    Internal.vectorLoop funcType 79 { bytes := artifactBytes, pos := 675, limit := 1622 } =
      .ok (Cache.raw.types.drop 74, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type74_decoded types_tail75_decoded

theorem types_tail73_decoded :
    Internal.vectorLoop funcType 80 { bytes := artifactBytes, pos := 652, limit := 1622 } =
      .ok (Cache.raw.types.drop 73, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type73_decoded types_tail74_decoded

theorem types_tail72_decoded :
    Internal.vectorLoop funcType 81 { bytes := artifactBytes, pos := 638, limit := 1622 } =
      .ok (Cache.raw.types.drop 72, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type72_decoded types_tail73_decoded

theorem types_tail71_decoded :
    Internal.vectorLoop funcType 82 { bytes := artifactBytes, pos := 616, limit := 1622 } =
      .ok (Cache.raw.types.drop 71, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type71_decoded types_tail72_decoded

theorem types_tail70_decoded :
    Internal.vectorLoop funcType 83 { bytes := artifactBytes, pos := 603, limit := 1622 } =
      .ok (Cache.raw.types.drop 70, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type70_decoded types_tail71_decoded

theorem types_tail69_decoded :
    Internal.vectorLoop funcType 84 { bytes := artifactBytes, pos := 588, limit := 1622 } =
      .ok (Cache.raw.types.drop 69, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type69_decoded types_tail70_decoded

theorem types_tail68_decoded :
    Internal.vectorLoop funcType 85 { bytes := artifactBytes, pos := 576, limit := 1622 } =
      .ok (Cache.raw.types.drop 68, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type68_decoded types_tail69_decoded

theorem types_tail67_decoded :
    Internal.vectorLoop funcType 86 { bytes := artifactBytes, pos := 559, limit := 1622 } =
      .ok (Cache.raw.types.drop 67, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type67_decoded types_tail68_decoded

theorem types_tail66_decoded :
    Internal.vectorLoop funcType 87 { bytes := artifactBytes, pos := 550, limit := 1622 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type66_decoded types_tail67_decoded

theorem types_tail65_decoded :
    Internal.vectorLoop funcType 88 { bytes := artifactBytes, pos := 530, limit := 1622 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type65_decoded types_tail66_decoded

theorem types_tail64_decoded :
    Internal.vectorLoop funcType 89 { bytes := artifactBytes, pos := 522, limit := 1622 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type64_decoded types_tail65_decoded

theorem types_tail63_decoded :
    Internal.vectorLoop funcType 90 { bytes := artifactBytes, pos := 515, limit := 1622 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type63_decoded types_tail64_decoded

theorem types_tail62_decoded :
    Internal.vectorLoop funcType 91 { bytes := artifactBytes, pos := 500, limit := 1622 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type62_decoded types_tail63_decoded

theorem types_tail61_decoded :
    Internal.vectorLoop funcType 92 { bytes := artifactBytes, pos := 494, limit := 1622 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type61_decoded types_tail62_decoded

theorem types_tail60_decoded :
    Internal.vectorLoop funcType 93 { bytes := artifactBytes, pos := 486, limit := 1622 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type60_decoded types_tail61_decoded

theorem types_tail59_decoded :
    Internal.vectorLoop funcType 94 { bytes := artifactBytes, pos := 471, limit := 1622 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type59_decoded types_tail60_decoded

theorem types_tail58_decoded :
    Internal.vectorLoop funcType 95 { bytes := artifactBytes, pos := 463, limit := 1622 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type58_decoded types_tail59_decoded

theorem types_tail57_decoded :
    Internal.vectorLoop funcType 96 { bytes := artifactBytes, pos := 429, limit := 1622 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type57_decoded types_tail58_decoded

theorem types_tail56_decoded :
    Internal.vectorLoop funcType 97 { bytes := artifactBytes, pos := 417, limit := 1622 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type56_decoded types_tail57_decoded

theorem types_tail55_decoded :
    Internal.vectorLoop funcType 98 { bytes := artifactBytes, pos := 406, limit := 1622 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type55_decoded types_tail56_decoded

theorem types_tail54_decoded :
    Internal.vectorLoop funcType 99 { bytes := artifactBytes, pos := 398, limit := 1622 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type54_decoded types_tail55_decoded

theorem types_tail53_decoded :
    Internal.vectorLoop funcType 100 { bytes := artifactBytes, pos := 390, limit := 1622 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type53_decoded types_tail54_decoded

theorem types_tail52_decoded :
    Internal.vectorLoop funcType 101 { bytes := artifactBytes, pos := 382, limit := 1622 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type52_decoded types_tail53_decoded

theorem types_tail51_decoded :
    Internal.vectorLoop funcType 102 { bytes := artifactBytes, pos := 376, limit := 1622 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type51_decoded types_tail52_decoded

theorem types_tail50_decoded :
    Internal.vectorLoop funcType 103 { bytes := artifactBytes, pos := 370, limit := 1622 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type50_decoded types_tail51_decoded

theorem types_tail49_decoded :
    Internal.vectorLoop funcType 104 { bytes := artifactBytes, pos := 363, limit := 1622 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50_decoded

theorem types_tail48_decoded :
    Internal.vectorLoop funcType 105 { bytes := artifactBytes, pos := 358, limit := 1622 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49_decoded

theorem types_tail47_decoded :
    Internal.vectorLoop funcType 106 { bytes := artifactBytes, pos := 353, limit := 1622 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48_decoded

theorem types_tail46_decoded :
    Internal.vectorLoop funcType 107 { bytes := artifactBytes, pos := 346, limit := 1622 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47_decoded

theorem types_tail45_decoded :
    Internal.vectorLoop funcType 108 { bytes := artifactBytes, pos := 332, limit := 1622 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46_decoded

theorem types_tail44_decoded :
    Internal.vectorLoop funcType 109 { bytes := artifactBytes, pos := 318, limit := 1622 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop funcType 110 { bytes := artifactBytes, pos := 309, limit := 1622 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop funcType 111 { bytes := artifactBytes, pos := 301, limit := 1622 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop funcType 112 { bytes := artifactBytes, pos := 293, limit := 1622 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop funcType 113 { bytes := artifactBytes, pos := 285, limit := 1622 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop funcType 114 { bytes := artifactBytes, pos := 277, limit := 1622 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop funcType 115 { bytes := artifactBytes, pos := 268, limit := 1622 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop funcType 116 { bytes := artifactBytes, pos := 259, limit := 1622 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop funcType 117 { bytes := artifactBytes, pos := 252, limit := 1622 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37_decoded

theorem types_tail35_decoded :
    Internal.vectorLoop funcType 118 { bytes := artifactBytes, pos := 243, limit := 1622 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop funcType 119 { bytes := artifactBytes, pos := 234, limit := 1622 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop funcType 120 { bytes := artifactBytes, pos := 225, limit := 1622 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop funcType 121 { bytes := artifactBytes, pos := 217, limit := 1622 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop funcType 122 { bytes := artifactBytes, pos := 209, limit := 1622 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop funcType 123 { bytes := artifactBytes, pos := 201, limit := 1622 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop funcType 124 { bytes := artifactBytes, pos := 193, limit := 1622 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop funcType 125 { bytes := artifactBytes, pos := 185, limit := 1622 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop funcType 126 { bytes := artifactBytes, pos := 178, limit := 1622 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop funcType 127 { bytes := artifactBytes, pos := 172, limit := 1622 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop funcType 128 { bytes := artifactBytes, pos := 167, limit := 1622 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop funcType 129 { bytes := artifactBytes, pos := 162, limit := 1622 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop funcType 130 { bytes := artifactBytes, pos := 154, limit := 1622 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop funcType 131 { bytes := artifactBytes, pos := 146, limit := 1622 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop funcType 132 { bytes := artifactBytes, pos := 138, limit := 1622 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 133 { bytes := artifactBytes, pos := 132, limit := 1622 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21_decoded

theorem types_tail19_decoded :
    Internal.vectorLoop funcType 134 { bytes := artifactBytes, pos := 126, limit := 1622 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 135 { bytes := artifactBytes, pos := 118, limit := 1622 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 136 { bytes := artifactBytes, pos := 112, limit := 1622 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 137 { bytes := artifactBytes, pos := 106, limit := 1622 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 138 { bytes := artifactBytes, pos := 100, limit := 1622 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 139 { bytes := artifactBytes, pos := 92, limit := 1622 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 140 { bytes := artifactBytes, pos := 87, limit := 1622 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 141 { bytes := artifactBytes, pos := 81, limit := 1622 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 142 { bytes := artifactBytes, pos := 76, limit := 1622 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 143 { bytes := artifactBytes, pos := 71, limit := 1622 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 144 { bytes := artifactBytes, pos := 66, limit := 1622 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 145 { bytes := artifactBytes, pos := 58, limit := 1622 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 146 { bytes := artifactBytes, pos := 53, limit := 1622 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 147 { bytes := artifactBytes, pos := 48, limit := 1622 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 148 { bytes := artifactBytes, pos := 43, limit := 1622 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 149 { bytes := artifactBytes, pos := 34, limit := 1622 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded

theorem types_tail3_decoded :
    Internal.vectorLoop funcType 150 { bytes := artifactBytes, pos := 29, limit := 1622 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 151 { bytes := artifactBytes, pos := 23, limit := 1622 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 152 { bytes := artifactBytes, pos := 17, limit := 1622 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 153 { bytes := artifactBytes, pos := 13, limit := 1622 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 1622 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by
  refine vector_eq_of_parts (length := 153)
    (itemsStart := { bytes := artifactBytes, pos := 13, limit := 1622 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded


end Project.EulerReconstructed.Artifact
