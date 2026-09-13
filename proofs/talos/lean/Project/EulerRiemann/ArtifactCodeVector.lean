import Project.EulerRiemann.ArtifactCode0
import Project.EulerRiemann.ArtifactCode99
import Project.EulerRiemann.ArtifactCode22
import Project.EulerRiemann.ArtifactCode54
import Project.EulerRiemann.ArtifactCode65
import Project.EulerRiemann.ArtifactCode77
import Project.EulerRiemann.ArtifactCode81
import Project.EulerRiemann.ArtifactCode85
import Project.EulerRiemann.ArtifactCode95
import Project.EulerRiemann.ArtifactCode96
import Project.EulerRiemann.ArtifactCode97
import Project.EulerRiemann.ArtifactCodes1To19
import Project.EulerRiemann.ArtifactCodes20To39
import Project.EulerRiemann.ArtifactCodes40To56
import Project.EulerRiemann.ArtifactCodes57To82
import Project.EulerRiemann.ArtifactCodes83To93
import Project.EulerRiemann.ArtifactCodes94To106
import Project.EulerRiemann.ArtifactCodes107

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072

theorem codes_tail108_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 21767, limit := 21767 } =
      .ok (Cache.raw.codes.drop 108, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by rfl

theorem codes_tail107_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 21414, limit := 21767 } =
      .ok (Cache.raw.codes.drop 107, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code107_decoded codes_tail108_decoded

theorem codes_tail106_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 21333, limit := 21767 } =
      .ok (Cache.raw.codes.drop 106, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code106_decoded codes_tail107_decoded

theorem codes_tail105_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 21305, limit := 21767 } =
      .ok (Cache.raw.codes.drop 105, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code105_decoded codes_tail106_decoded

theorem codes_tail104_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 20938, limit := 21767 } =
      .ok (Cache.raw.codes.drop 104, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code104_decoded codes_tail105_decoded

theorem codes_tail103_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 20859, limit := 21767 } =
      .ok (Cache.raw.codes.drop 103, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code103_decoded codes_tail104_decoded

theorem codes_tail102_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 20842, limit := 21767 } =
      .ok (Cache.raw.codes.drop 102, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code102_decoded codes_tail103_decoded

theorem codes_tail101_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 20831, limit := 21767 } =
      .ok (Cache.raw.codes.drop 101, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code101_decoded codes_tail102_decoded

theorem codes_tail100_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 20820, limit := 21767 } =
      .ok (Cache.raw.codes.drop 100, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code100_decoded codes_tail101_decoded

theorem codes_tail99_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 18034, limit := 21767 } =
      .ok (Cache.raw.codes.drop 99, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code99_decoded codes_tail100_decoded

theorem codes_tail98_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 18023, limit := 21767 } =
      .ok (Cache.raw.codes.drop 98, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code98_decoded codes_tail99_decoded

theorem codes_tail97_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 17501, limit := 21767 } =
      .ok (Cache.raw.codes.drop 97, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code97_decoded codes_tail98_decoded

theorem codes_tail96_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 16415, limit := 21767 } =
      .ok (Cache.raw.codes.drop 96, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code96_decoded codes_tail97_decoded

theorem codes_tail95_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 13877, limit := 21767 } =
      .ok (Cache.raw.codes.drop 95, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code95_decoded codes_tail96_decoded

theorem codes_tail94_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 13255, limit := 21767 } =
      .ok (Cache.raw.codes.drop 94, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code94_decoded codes_tail95_decoded

theorem codes_tail93_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 12877, limit := 21767 } =
      .ok (Cache.raw.codes.drop 93, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code93_decoded codes_tail94_decoded

theorem codes_tail92_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 12798, limit := 21767 } =
      .ok (Cache.raw.codes.drop 92, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code92_decoded codes_tail93_decoded

theorem codes_tail91_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 12711, limit := 21767 } =
      .ok (Cache.raw.codes.drop 91, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code91_decoded codes_tail92_decoded

theorem codes_tail90_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 12624, limit := 21767 } =
      .ok (Cache.raw.codes.drop 90, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code90_decoded codes_tail91_decoded

theorem codes_tail89_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 12529, limit := 21767 } =
      .ok (Cache.raw.codes.drop 89, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code89_decoded codes_tail90_decoded

theorem codes_tail88_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 12430, limit := 21767 } =
      .ok (Cache.raw.codes.drop 88, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code88_decoded codes_tail89_decoded

theorem codes_tail87_decoded :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 12317, limit := 21767 } =
      .ok (Cache.raw.codes.drop 87, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code87_decoded codes_tail88_decoded

theorem codes_tail86_decoded :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 12150, limit := 21767 } =
      .ok (Cache.raw.codes.drop 86, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code86_decoded codes_tail87_decoded

theorem codes_tail85_decoded :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 11645, limit := 21767 } =
      .ok (Cache.raw.codes.drop 85, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code85_decoded codes_tail86_decoded

theorem codes_tail84_decoded :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 11628, limit := 21767 } =
      .ok (Cache.raw.codes.drop 84, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code84_decoded codes_tail85_decoded

theorem codes_tail83_decoded :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 11617, limit := 21767 } =
      .ok (Cache.raw.codes.drop 83, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code83_decoded codes_tail84_decoded

theorem codes_tail82_decoded :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 11606, limit := 21767 } =
      .ok (Cache.raw.codes.drop 82, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code82_decoded codes_tail83_decoded

theorem codes_tail81_decoded :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 10473, limit := 21767 } =
      .ok (Cache.raw.codes.drop 81, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code81_decoded codes_tail82_decoded

theorem codes_tail80_decoded :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 10314, limit := 21767 } =
      .ok (Cache.raw.codes.drop 80, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code80_decoded codes_tail81_decoded

theorem codes_tail79_decoded :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 10067, limit := 21767 } =
      .ok (Cache.raw.codes.drop 79, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code79_decoded codes_tail80_decoded

theorem codes_tail78_decoded :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 10056, limit := 21767 } =
      .ok (Cache.raw.codes.drop 78, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code78_decoded codes_tail79_decoded

theorem codes_tail77_decoded :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 9220, limit := 21767 } =
      .ok (Cache.raw.codes.drop 77, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code77_decoded codes_tail78_decoded

theorem codes_tail76_decoded :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 8856, limit := 21767 } =
      .ok (Cache.raw.codes.drop 76, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code76_decoded codes_tail77_decoded

theorem codes_tail75_decoded :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 8845, limit := 21767 } =
      .ok (Cache.raw.codes.drop 75, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code75_decoded codes_tail76_decoded

theorem codes_tail74_decoded :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 8834, limit := 21767 } =
      .ok (Cache.raw.codes.drop 74, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code74_decoded codes_tail75_decoded

theorem codes_tail73_decoded :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 8823, limit := 21767 } =
      .ok (Cache.raw.codes.drop 73, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code73_decoded codes_tail74_decoded

theorem codes_tail72_decoded :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 8812, limit := 21767 } =
      .ok (Cache.raw.codes.drop 72, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code72_decoded codes_tail73_decoded

theorem codes_tail71_decoded :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 8801, limit := 21767 } =
      .ok (Cache.raw.codes.drop 71, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code71_decoded codes_tail72_decoded

theorem codes_tail70_decoded :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 8790, limit := 21767 } =
      .ok (Cache.raw.codes.drop 70, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code70_decoded codes_tail71_decoded

theorem codes_tail69_decoded :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 8640, limit := 21767 } =
      .ok (Cache.raw.codes.drop 69, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code69_decoded codes_tail70_decoded

theorem codes_tail68_decoded :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 8611, limit := 21767 } =
      .ok (Cache.raw.codes.drop 68, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code68_decoded codes_tail69_decoded

theorem codes_tail67_decoded :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 8582, limit := 21767 } =
      .ok (Cache.raw.codes.drop 67, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code67_decoded codes_tail68_decoded

theorem codes_tail66_decoded :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 8553, limit := 21767 } =
      .ok (Cache.raw.codes.drop 66, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code66_decoded codes_tail67_decoded

theorem codes_tail65_decoded :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 7377, limit := 21767 } =
      .ok (Cache.raw.codes.drop 65, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code65_decoded codes_tail66_decoded

theorem codes_tail64_decoded :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 7324, limit := 21767 } =
      .ok (Cache.raw.codes.drop 64, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code64_decoded codes_tail65_decoded

theorem codes_tail63_decoded :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 7313, limit := 21767 } =
      .ok (Cache.raw.codes.drop 63, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code63_decoded codes_tail64_decoded

theorem codes_tail62_decoded :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 7302, limit := 21767 } =
      .ok (Cache.raw.codes.drop 62, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code62_decoded codes_tail63_decoded

theorem codes_tail61_decoded :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 7291, limit := 21767 } =
      .ok (Cache.raw.codes.drop 61, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code61_decoded codes_tail62_decoded

theorem codes_tail60_decoded :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 7280, limit := 21767 } =
      .ok (Cache.raw.codes.drop 60, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code60_decoded codes_tail61_decoded

theorem codes_tail59_decoded :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 7269, limit := 21767 } =
      .ok (Cache.raw.codes.drop 59, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code59_decoded codes_tail60_decoded

theorem codes_tail58_decoded :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 7222, limit := 21767 } =
      .ok (Cache.raw.codes.drop 58, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code58_decoded codes_tail59_decoded

theorem codes_tail57_decoded :
    Internal.vectorLoop code 51 { bytes := artifactBytes, pos := 6978, limit := 21767 } =
      .ok (Cache.raw.codes.drop 57, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code57_decoded codes_tail58_decoded

theorem codes_tail56_decoded :
    Internal.vectorLoop code 52 { bytes := artifactBytes, pos := 6967, limit := 21767 } =
      .ok (Cache.raw.codes.drop 56, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code56_decoded codes_tail57_decoded

theorem codes_tail55_decoded :
    Internal.vectorLoop code 53 { bytes := artifactBytes, pos := 6956, limit := 21767 } =
      .ok (Cache.raw.codes.drop 55, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code55_decoded codes_tail56_decoded

theorem codes_tail54_decoded :
    Internal.vectorLoop code 54 { bytes := artifactBytes, pos := 6300, limit := 21767 } =
      .ok (Cache.raw.codes.drop 54, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code54_decoded codes_tail55_decoded

theorem codes_tail53_decoded :
    Internal.vectorLoop code 55 { bytes := artifactBytes, pos := 6259, limit := 21767 } =
      .ok (Cache.raw.codes.drop 53, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code53_decoded codes_tail54_decoded

theorem codes_tail52_decoded :
    Internal.vectorLoop code 56 { bytes := artifactBytes, pos := 6248, limit := 21767 } =
      .ok (Cache.raw.codes.drop 52, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code52_decoded codes_tail53_decoded

theorem codes_tail51_decoded :
    Internal.vectorLoop code 57 { bytes := artifactBytes, pos := 6237, limit := 21767 } =
      .ok (Cache.raw.codes.drop 51, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code51_decoded codes_tail52_decoded

theorem codes_tail50_decoded :
    Internal.vectorLoop code 58 { bytes := artifactBytes, pos := 6226, limit := 21767 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code50_decoded codes_tail51_decoded

theorem codes_tail49_decoded :
    Internal.vectorLoop code 59 { bytes := artifactBytes, pos := 6215, limit := 21767 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50_decoded

theorem codes_tail48_decoded :
    Internal.vectorLoop code 60 { bytes := artifactBytes, pos := 6204, limit := 21767 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49_decoded

theorem codes_tail47_decoded :
    Internal.vectorLoop code 61 { bytes := artifactBytes, pos := 6193, limit := 21767 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48_decoded

theorem codes_tail46_decoded :
    Internal.vectorLoop code 62 { bytes := artifactBytes, pos := 6140, limit := 21767 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47_decoded

theorem codes_tail45_decoded :
    Internal.vectorLoop code 63 { bytes := artifactBytes, pos := 5778, limit := 21767 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46_decoded

theorem codes_tail44_decoded :
    Internal.vectorLoop code 64 { bytes := artifactBytes, pos := 5761, limit := 21767 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45_decoded

theorem codes_tail43_decoded :
    Internal.vectorLoop code 65 { bytes := artifactBytes, pos := 5724, limit := 21767 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44_decoded

theorem codes_tail42_decoded :
    Internal.vectorLoop code 66 { bytes := artifactBytes, pos := 5701, limit := 21767 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43_decoded

theorem codes_tail41_decoded :
    Internal.vectorLoop code 67 { bytes := artifactBytes, pos := 5659, limit := 21767 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42_decoded

theorem codes_tail40_decoded :
    Internal.vectorLoop code 68 { bytes := artifactBytes, pos := 5013, limit := 21767 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41_decoded

theorem codes_tail39_decoded :
    Internal.vectorLoop code 69 { bytes := artifactBytes, pos := 4947, limit := 21767 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40_decoded

theorem codes_tail38_decoded :
    Internal.vectorLoop code 70 { bytes := artifactBytes, pos := 4936, limit := 21767 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39_decoded

theorem codes_tail37_decoded :
    Internal.vectorLoop code 71 { bytes := artifactBytes, pos := 4701, limit := 21767 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38_decoded

theorem codes_tail36_decoded :
    Internal.vectorLoop code 72 { bytes := artifactBytes, pos := 4638, limit := 21767 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37_decoded

theorem codes_tail35_decoded :
    Internal.vectorLoop code 73 { bytes := artifactBytes, pos := 4552, limit := 21767 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36_decoded

theorem codes_tail34_decoded :
    Internal.vectorLoop code 74 { bytes := artifactBytes, pos := 4521, limit := 21767 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35_decoded

theorem codes_tail33_decoded :
    Internal.vectorLoop code 75 { bytes := artifactBytes, pos := 4312, limit := 21767 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34_decoded

theorem codes_tail32_decoded :
    Internal.vectorLoop code 76 { bytes := artifactBytes, pos := 3978, limit := 21767 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33_decoded

theorem codes_tail31_decoded :
    Internal.vectorLoop code 77 { bytes := artifactBytes, pos := 3805, limit := 21767 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32_decoded

theorem codes_tail30_decoded :
    Internal.vectorLoop code 78 { bytes := artifactBytes, pos := 3794, limit := 21767 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31_decoded

theorem codes_tail29_decoded :
    Internal.vectorLoop code 79 { bytes := artifactBytes, pos := 3783, limit := 21767 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30_decoded

theorem codes_tail28_decoded :
    Internal.vectorLoop code 80 { bytes := artifactBytes, pos := 3772, limit := 21767 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29_decoded

theorem codes_tail27_decoded :
    Internal.vectorLoop code 81 { bytes := artifactBytes, pos := 3761, limit := 21767 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28_decoded

theorem codes_tail26_decoded :
    Internal.vectorLoop code 82 { bytes := artifactBytes, pos := 3750, limit := 21767 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27_decoded

theorem codes_tail25_decoded :
    Internal.vectorLoop code 83 { bytes := artifactBytes, pos := 3739, limit := 21767 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26_decoded

theorem codes_tail24_decoded :
    Internal.vectorLoop code 84 { bytes := artifactBytes, pos := 3728, limit := 21767 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25_decoded

theorem codes_tail23_decoded :
    Internal.vectorLoop code 85 { bytes := artifactBytes, pos := 3717, limit := 21767 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24_decoded

theorem codes_tail22_decoded :
    Internal.vectorLoop code 86 { bytes := artifactBytes, pos := 2876, limit := 21767 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23_decoded

theorem codes_tail21_decoded :
    Internal.vectorLoop code 87 { bytes := artifactBytes, pos := 2823, limit := 21767 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22_decoded

theorem codes_tail20_decoded :
    Internal.vectorLoop code 88 { bytes := artifactBytes, pos := 2740, limit := 21767 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21_decoded

theorem codes_tail19_decoded :
    Internal.vectorLoop code 89 { bytes := artifactBytes, pos := 2409, limit := 21767 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 90 { bytes := artifactBytes, pos := 2273, limit := 21767 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 91 { bytes := artifactBytes, pos := 2205, limit := 21767 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 92 { bytes := artifactBytes, pos := 2089, limit := 21767 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 93 { bytes := artifactBytes, pos := 2014, limit := 21767 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 94 { bytes := artifactBytes, pos := 1955, limit := 21767 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 95 { bytes := artifactBytes, pos := 1923, limit := 21767 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 96 { bytes := artifactBytes, pos := 1841, limit := 21767 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 97 { bytes := artifactBytes, pos := 1742, limit := 21767 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 98 { bytes := artifactBytes, pos := 1696, limit := 21767 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 99 { bytes := artifactBytes, pos := 1674, limit := 21767 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 100 { bytes := artifactBytes, pos := 1637, limit := 21767 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 101 { bytes := artifactBytes, pos := 1614, limit := 21767 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 102 { bytes := artifactBytes, pos := 1572, limit := 21767 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 103 { bytes := artifactBytes, pos := 1444, limit := 21767 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 104 { bytes := artifactBytes, pos := 1407, limit := 21767 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded

theorem codes_tail3_decoded :
    Internal.vectorLoop code 105 { bytes := artifactBytes, pos := 1384, limit := 21767 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 106 { bytes := artifactBytes, pos := 1342, limit := 21767 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 107 { bytes := artifactBytes, pos := 1313, limit := 21767 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 108 { bytes := artifactBytes, pos := 1294, limit := 21767 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 1293, limit := 21767 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine vector_eq_of_parts (length := 108) (itemsStart := { bytes := artifactBytes, pos := 1294, limit := 21767 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 1290, limit := 21767 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine sized_eq_of_parts (size := 20474) (payload := { bytes := artifactBytes, pos := 1293, limit := 21767 })
    (finish := { bytes := artifactBytes, pos := 21767, limit := 21767 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.EulerRiemann.Artifact
