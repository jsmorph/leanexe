import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstructed.ArtifactCodes0To7
import Project.EulerReconstructed.ArtifactCodes8To15
import Project.EulerReconstructed.ArtifactCodes16To23
import Project.EulerReconstructed.ArtifactCodes24To31
import Project.EulerReconstructed.ArtifactCodes32To39
import Project.EulerReconstructed.ArtifactCodes40To47
import Project.EulerReconstructed.ArtifactCodes48To55
import Project.EulerReconstructed.ArtifactCodes56To63
import Project.EulerReconstructed.ArtifactCodes64To71
import Project.EulerReconstructed.ArtifactCodes72To79
import Project.EulerReconstructed.ArtifactCodes80To87
import Project.EulerReconstructed.ArtifactCodes88To95
import Project.EulerReconstructed.ArtifactCodes96To103
import Project.EulerReconstructed.ArtifactCodes104To111
import Project.EulerReconstructed.ArtifactCodes112To119
import Project.EulerReconstructed.ArtifactCodes120To127
import Project.EulerReconstructed.ArtifactCodes128To135
import Project.EulerReconstructed.ArtifactCodes136To143
import Project.EulerReconstructed.ArtifactCodes144To151
import Project.EulerReconstructed.ArtifactCodes152To152

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail153_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 30726, limit := 30726 } =
      .ok (Cache.raw.codes.drop 153, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by rfl

theorem codes_tail152_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 30371, limit := 30726 } =
      .ok (Cache.raw.codes.drop 152, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code152_decoded codes_tail153_decoded

theorem codes_tail151_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 30290, limit := 30726 } =
      .ok (Cache.raw.codes.drop 151, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code151_decoded codes_tail152_decoded

theorem codes_tail150_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 30262, limit := 30726 } =
      .ok (Cache.raw.codes.drop 150, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code150_decoded codes_tail151_decoded

theorem codes_tail149_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 29895, limit := 30726 } =
      .ok (Cache.raw.codes.drop 149, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code149_decoded codes_tail150_decoded

theorem codes_tail148_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 29808, limit := 30726 } =
      .ok (Cache.raw.codes.drop 148, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code148_decoded codes_tail149_decoded

theorem codes_tail147_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 29791, limit := 30726 } =
      .ok (Cache.raw.codes.drop 147, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code147_decoded codes_tail148_decoded

theorem codes_tail146_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 29780, limit := 30726 } =
      .ok (Cache.raw.codes.drop 146, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code146_decoded codes_tail147_decoded

theorem codes_tail145_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 29769, limit := 30726 } =
      .ok (Cache.raw.codes.drop 145, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code145_decoded codes_tail146_decoded

theorem codes_tail144_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 26980, limit := 30726 } =
      .ok (Cache.raw.codes.drop 144, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code144_decoded codes_tail145_decoded

theorem codes_tail143_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 26969, limit := 30726 } =
      .ok (Cache.raw.codes.drop 143, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code143_decoded codes_tail144_decoded

theorem codes_tail142_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 26439, limit := 30726 } =
      .ok (Cache.raw.codes.drop 142, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code142_decoded codes_tail143_decoded

theorem codes_tail141_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 25350, limit := 30726 } =
      .ok (Cache.raw.codes.drop 141, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code141_decoded codes_tail142_decoded

theorem codes_tail140_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 22810, limit := 30726 } =
      .ok (Cache.raw.codes.drop 140, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code140_decoded codes_tail141_decoded

theorem codes_tail139_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 22186, limit := 30726 } =
      .ok (Cache.raw.codes.drop 139, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code139_decoded codes_tail140_decoded

theorem codes_tail138_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 21345, limit := 30726 } =
      .ok (Cache.raw.codes.drop 138, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code138_decoded codes_tail139_decoded

theorem codes_tail137_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 20945, limit := 30726 } =
      .ok (Cache.raw.codes.drop 137, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code137_decoded codes_tail138_decoded

theorem codes_tail136_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 20865, limit := 30726 } =
      .ok (Cache.raw.codes.drop 136, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code136_decoded codes_tail137_decoded

theorem codes_tail135_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 20777, limit := 30726 } =
      .ok (Cache.raw.codes.drop 135, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code135_decoded codes_tail136_decoded

theorem codes_tail134_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 20689, limit := 30726 } =
      .ok (Cache.raw.codes.drop 134, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code134_decoded codes_tail135_decoded

theorem codes_tail133_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 20593, limit := 30726 } =
      .ok (Cache.raw.codes.drop 133, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code133_decoded codes_tail134_decoded

theorem codes_tail132_decoded :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 20494, limit := 30726 } =
      .ok (Cache.raw.codes.drop 132, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code132_decoded codes_tail133_decoded

theorem codes_tail131_decoded :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 20381, limit := 30726 } =
      .ok (Cache.raw.codes.drop 131, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code131_decoded codes_tail132_decoded

theorem codes_tail130_decoded :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 20214, limit := 30726 } =
      .ok (Cache.raw.codes.drop 130, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code130_decoded codes_tail131_decoded

theorem codes_tail129_decoded :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 19684, limit := 30726 } =
      .ok (Cache.raw.codes.drop 129, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code129_decoded codes_tail130_decoded

theorem codes_tail128_decoded :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 19667, limit := 30726 } =
      .ok (Cache.raw.codes.drop 128, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code128_decoded codes_tail129_decoded

theorem codes_tail127_decoded :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 19656, limit := 30726 } =
      .ok (Cache.raw.codes.drop 127, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code127_decoded codes_tail128_decoded

theorem codes_tail126_decoded :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 19645, limit := 30726 } =
      .ok (Cache.raw.codes.drop 126, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code126_decoded codes_tail127_decoded

theorem codes_tail125_decoded :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 18277, limit := 30726 } =
      .ok (Cache.raw.codes.drop 125, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code125_decoded codes_tail126_decoded

theorem codes_tail124_decoded :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 18105, limit := 30726 } =
      .ok (Cache.raw.codes.drop 124, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code124_decoded codes_tail125_decoded

theorem codes_tail123_decoded :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 17858, limit := 30726 } =
      .ok (Cache.raw.codes.drop 123, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code123_decoded codes_tail124_decoded

theorem codes_tail122_decoded :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 17847, limit := 30726 } =
      .ok (Cache.raw.codes.drop 122, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code122_decoded codes_tail123_decoded

theorem codes_tail121_decoded :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 17005, limit := 30726 } =
      .ok (Cache.raw.codes.drop 121, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code121_decoded codes_tail122_decoded

theorem codes_tail120_decoded :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 16539, limit := 30726 } =
      .ok (Cache.raw.codes.drop 120, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code120_decoded codes_tail121_decoded

theorem codes_tail119_decoded :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 16528, limit := 30726 } =
      .ok (Cache.raw.codes.drop 119, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code119_decoded codes_tail120_decoded

theorem codes_tail118_decoded :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 16517, limit := 30726 } =
      .ok (Cache.raw.codes.drop 118, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code118_decoded codes_tail119_decoded

theorem codes_tail117_decoded :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 16506, limit := 30726 } =
      .ok (Cache.raw.codes.drop 117, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code117_decoded codes_tail118_decoded

theorem codes_tail116_decoded :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 16495, limit := 30726 } =
      .ok (Cache.raw.codes.drop 116, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code116_decoded codes_tail117_decoded

theorem codes_tail115_decoded :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 16484, limit := 30726 } =
      .ok (Cache.raw.codes.drop 115, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code115_decoded codes_tail116_decoded

theorem codes_tail114_decoded :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 16473, limit := 30726 } =
      .ok (Cache.raw.codes.drop 114, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code114_decoded codes_tail115_decoded

theorem codes_tail113_decoded :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 16444, limit := 30726 } =
      .ok (Cache.raw.codes.drop 113, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code113_decoded codes_tail114_decoded

theorem codes_tail112_decoded :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 16415, limit := 30726 } =
      .ok (Cache.raw.codes.drop 112, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code112_decoded codes_tail113_decoded

theorem codes_tail111_decoded :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 16386, limit := 30726 } =
      .ok (Cache.raw.codes.drop 111, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code111_decoded codes_tail112_decoded

theorem codes_tail110_decoded :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 16357, limit := 30726 } =
      .ok (Cache.raw.codes.drop 110, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code110_decoded codes_tail111_decoded

theorem codes_tail109_decoded :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 16328, limit := 30726 } =
      .ok (Cache.raw.codes.drop 109, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code109_decoded codes_tail110_decoded

theorem codes_tail108_decoded :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 15529, limit := 30726 } =
      .ok (Cache.raw.codes.drop 108, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code108_decoded codes_tail109_decoded

theorem codes_tail107_decoded :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 15500, limit := 30726 } =
      .ok (Cache.raw.codes.drop 107, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code107_decoded codes_tail108_decoded

theorem codes_tail106_decoded :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 15471, limit := 30726 } =
      .ok (Cache.raw.codes.drop 106, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code106_decoded codes_tail107_decoded

theorem codes_tail105_decoded :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 15125, limit := 30726 } =
      .ok (Cache.raw.codes.drop 105, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code105_decoded codes_tail106_decoded

theorem codes_tail104_decoded :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 14248, limit := 30726 } =
      .ok (Cache.raw.codes.drop 104, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code104_decoded codes_tail105_decoded

theorem codes_tail103_decoded :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 14195, limit := 30726 } =
      .ok (Cache.raw.codes.drop 103, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code103_decoded codes_tail104_decoded

theorem codes_tail102_decoded :
    Internal.vectorLoop code 51 { bytes := artifactBytes, pos := 14184, limit := 30726 } =
      .ok (Cache.raw.codes.drop 102, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code102_decoded codes_tail103_decoded

theorem codes_tail101_decoded :
    Internal.vectorLoop code 52 { bytes := artifactBytes, pos := 14173, limit := 30726 } =
      .ok (Cache.raw.codes.drop 101, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code101_decoded codes_tail102_decoded

theorem codes_tail100_decoded :
    Internal.vectorLoop code 53 { bytes := artifactBytes, pos := 14162, limit := 30726 } =
      .ok (Cache.raw.codes.drop 100, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code100_decoded codes_tail101_decoded

theorem codes_tail99_decoded :
    Internal.vectorLoop code 54 { bytes := artifactBytes, pos := 14151, limit := 30726 } =
      .ok (Cache.raw.codes.drop 99, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code99_decoded codes_tail100_decoded

theorem codes_tail98_decoded :
    Internal.vectorLoop code 55 { bytes := artifactBytes, pos := 14140, limit := 30726 } =
      .ok (Cache.raw.codes.drop 98, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code98_decoded codes_tail99_decoded

theorem codes_tail97_decoded :
    Internal.vectorLoop code 56 { bytes := artifactBytes, pos := 14093, limit := 30726 } =
      .ok (Cache.raw.codes.drop 97, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code97_decoded codes_tail98_decoded

theorem codes_tail96_decoded :
    Internal.vectorLoop code 57 { bytes := artifactBytes, pos := 13849, limit := 30726 } =
      .ok (Cache.raw.codes.drop 96, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code96_decoded codes_tail97_decoded

theorem codes_tail95_decoded :
    Internal.vectorLoop code 58 { bytes := artifactBytes, pos := 13838, limit := 30726 } =
      .ok (Cache.raw.codes.drop 95, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code95_decoded codes_tail96_decoded

theorem codes_tail94_decoded :
    Internal.vectorLoop code 59 { bytes := artifactBytes, pos := 13827, limit := 30726 } =
      .ok (Cache.raw.codes.drop 94, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code94_decoded codes_tail95_decoded

theorem codes_tail93_decoded :
    Internal.vectorLoop code 60 { bytes := artifactBytes, pos := 13171, limit := 30726 } =
      .ok (Cache.raw.codes.drop 93, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code93_decoded codes_tail94_decoded

theorem codes_tail92_decoded :
    Internal.vectorLoop code 61 { bytes := artifactBytes, pos := 13130, limit := 30726 } =
      .ok (Cache.raw.codes.drop 92, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code92_decoded codes_tail93_decoded

theorem codes_tail91_decoded :
    Internal.vectorLoop code 62 { bytes := artifactBytes, pos := 13119, limit := 30726 } =
      .ok (Cache.raw.codes.drop 91, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code91_decoded codes_tail92_decoded

theorem codes_tail90_decoded :
    Internal.vectorLoop code 63 { bytes := artifactBytes, pos := 13108, limit := 30726 } =
      .ok (Cache.raw.codes.drop 90, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code90_decoded codes_tail91_decoded

theorem codes_tail89_decoded :
    Internal.vectorLoop code 64 { bytes := artifactBytes, pos := 13097, limit := 30726 } =
      .ok (Cache.raw.codes.drop 89, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code89_decoded codes_tail90_decoded

theorem codes_tail88_decoded :
    Internal.vectorLoop code 65 { bytes := artifactBytes, pos := 13086, limit := 30726 } =
      .ok (Cache.raw.codes.drop 88, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code88_decoded codes_tail89_decoded

theorem codes_tail87_decoded :
    Internal.vectorLoop code 66 { bytes := artifactBytes, pos := 13075, limit := 30726 } =
      .ok (Cache.raw.codes.drop 87, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code87_decoded codes_tail88_decoded

theorem codes_tail86_decoded :
    Internal.vectorLoop code 67 { bytes := artifactBytes, pos := 13064, limit := 30726 } =
      .ok (Cache.raw.codes.drop 86, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code86_decoded codes_tail87_decoded

theorem codes_tail85_decoded :
    Internal.vectorLoop code 68 { bytes := artifactBytes, pos := 13011, limit := 30726 } =
      .ok (Cache.raw.codes.drop 85, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code85_decoded codes_tail86_decoded

theorem codes_tail84_decoded :
    Internal.vectorLoop code 69 { bytes := artifactBytes, pos := 12649, limit := 30726 } =
      .ok (Cache.raw.codes.drop 84, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code84_decoded codes_tail85_decoded

theorem codes_tail83_decoded :
    Internal.vectorLoop code 70 { bytes := artifactBytes, pos := 12632, limit := 30726 } =
      .ok (Cache.raw.codes.drop 83, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code83_decoded codes_tail84_decoded

theorem codes_tail82_decoded :
    Internal.vectorLoop code 71 { bytes := artifactBytes, pos := 12595, limit := 30726 } =
      .ok (Cache.raw.codes.drop 82, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code82_decoded codes_tail83_decoded

theorem codes_tail81_decoded :
    Internal.vectorLoop code 72 { bytes := artifactBytes, pos := 12572, limit := 30726 } =
      .ok (Cache.raw.codes.drop 81, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code81_decoded codes_tail82_decoded

theorem codes_tail80_decoded :
    Internal.vectorLoop code 73 { bytes := artifactBytes, pos := 12530, limit := 30726 } =
      .ok (Cache.raw.codes.drop 80, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code80_decoded codes_tail81_decoded

theorem codes_tail79_decoded :
    Internal.vectorLoop code 74 { bytes := artifactBytes, pos := 12519, limit := 30726 } =
      .ok (Cache.raw.codes.drop 79, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code79_decoded codes_tail80_decoded

theorem codes_tail78_decoded :
    Internal.vectorLoop code 75 { bytes := artifactBytes, pos := 12508, limit := 30726 } =
      .ok (Cache.raw.codes.drop 78, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code78_decoded codes_tail79_decoded

theorem codes_tail77_decoded :
    Internal.vectorLoop code 76 { bytes := artifactBytes, pos := 11840, limit := 30726 } =
      .ok (Cache.raw.codes.drop 77, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code77_decoded codes_tail78_decoded

theorem codes_tail76_decoded :
    Internal.vectorLoop code 77 { bytes := artifactBytes, pos := 11787, limit := 30726 } =
      .ok (Cache.raw.codes.drop 76, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code76_decoded codes_tail77_decoded

theorem codes_tail75_decoded :
    Internal.vectorLoop code 78 { bytes := artifactBytes, pos := 11242, limit := 30726 } =
      .ok (Cache.raw.codes.drop 75, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code75_decoded codes_tail76_decoded

theorem codes_tail74_decoded :
    Internal.vectorLoop code 79 { bytes := artifactBytes, pos := 11213, limit := 30726 } =
      .ok (Cache.raw.codes.drop 74, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code74_decoded codes_tail75_decoded

theorem codes_tail73_decoded :
    Internal.vectorLoop code 80 { bytes := artifactBytes, pos := 10739, limit := 30726 } =
      .ok (Cache.raw.codes.drop 73, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code73_decoded codes_tail74_decoded

theorem codes_tail72_decoded :
    Internal.vectorLoop code 81 { bytes := artifactBytes, pos := 10728, limit := 30726 } =
      .ok (Cache.raw.codes.drop 72, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code72_decoded codes_tail73_decoded

theorem codes_tail71_decoded :
    Internal.vectorLoop code 82 { bytes := artifactBytes, pos := 10249, limit := 30726 } =
      .ok (Cache.raw.codes.drop 71, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code71_decoded codes_tail72_decoded

theorem codes_tail70_decoded :
    Internal.vectorLoop code 83 { bytes := artifactBytes, pos := 10164, limit := 30726 } =
      .ok (Cache.raw.codes.drop 70, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code70_decoded codes_tail71_decoded

theorem codes_tail69_decoded :
    Internal.vectorLoop code 84 { bytes := artifactBytes, pos := 10111, limit := 30726 } =
      .ok (Cache.raw.codes.drop 69, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code69_decoded codes_tail70_decoded

theorem codes_tail68_decoded :
    Internal.vectorLoop code 85 { bytes := artifactBytes, pos := 10058, limit := 30726 } =
      .ok (Cache.raw.codes.drop 68, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code68_decoded codes_tail69_decoded

theorem codes_tail67_decoded :
    Internal.vectorLoop code 86 { bytes := artifactBytes, pos := 9993, limit := 30726 } =
      .ok (Cache.raw.codes.drop 67, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code67_decoded codes_tail68_decoded

theorem codes_tail66_decoded :
    Internal.vectorLoop code 87 { bytes := artifactBytes, pos := 9982, limit := 30726 } =
      .ok (Cache.raw.codes.drop 66, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code66_decoded codes_tail67_decoded

theorem codes_tail65_decoded :
    Internal.vectorLoop code 88 { bytes := artifactBytes, pos := 9615, limit := 30726 } =
      .ok (Cache.raw.codes.drop 65, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code65_decoded codes_tail66_decoded

theorem codes_tail64_decoded :
    Internal.vectorLoop code 89 { bytes := artifactBytes, pos := 9570, limit := 30726 } =
      .ok (Cache.raw.codes.drop 64, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code64_decoded codes_tail65_decoded

theorem codes_tail63_decoded :
    Internal.vectorLoop code 90 { bytes := artifactBytes, pos := 9541, limit := 30726 } =
      .ok (Cache.raw.codes.drop 63, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code63_decoded codes_tail64_decoded

theorem codes_tail62_decoded :
    Internal.vectorLoop code 91 { bytes := artifactBytes, pos := 9448, limit := 30726 } =
      .ok (Cache.raw.codes.drop 62, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code62_decoded codes_tail63_decoded

theorem codes_tail61_decoded :
    Internal.vectorLoop code 92 { bytes := artifactBytes, pos := 9340, limit := 30726 } =
      .ok (Cache.raw.codes.drop 61, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code61_decoded codes_tail62_decoded

theorem codes_tail60_decoded :
    Internal.vectorLoop code 93 { bytes := artifactBytes, pos := 9257, limit := 30726 } =
      .ok (Cache.raw.codes.drop 60, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code60_decoded codes_tail61_decoded

theorem codes_tail59_decoded :
    Internal.vectorLoop code 94 { bytes := artifactBytes, pos := 9204, limit := 30726 } =
      .ok (Cache.raw.codes.drop 59, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code59_decoded codes_tail60_decoded

theorem codes_tail58_decoded :
    Internal.vectorLoop code 95 { bytes := artifactBytes, pos := 9165, limit := 30726 } =
      .ok (Cache.raw.codes.drop 58, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code58_decoded codes_tail59_decoded

theorem codes_tail57_decoded :
    Internal.vectorLoop code 96 { bytes := artifactBytes, pos := 7507, limit := 30726 } =
      .ok (Cache.raw.codes.drop 57, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code57_decoded codes_tail58_decoded

theorem codes_tail56_decoded :
    Internal.vectorLoop code 97 { bytes := artifactBytes, pos := 7441, limit := 30726 } =
      .ok (Cache.raw.codes.drop 56, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code56_decoded codes_tail57_decoded

theorem codes_tail55_decoded :
    Internal.vectorLoop code 98 { bytes := artifactBytes, pos := 7430, limit := 30726 } =
      .ok (Cache.raw.codes.drop 55, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code55_decoded codes_tail56_decoded

theorem codes_tail54_decoded :
    Internal.vectorLoop code 99 { bytes := artifactBytes, pos := 7195, limit := 30726 } =
      .ok (Cache.raw.codes.drop 54, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code54_decoded codes_tail55_decoded

theorem codes_tail53_decoded :
    Internal.vectorLoop code 100 { bytes := artifactBytes, pos := 7052, limit := 30726 } =
      .ok (Cache.raw.codes.drop 53, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code53_decoded codes_tail54_decoded

theorem codes_tail52_decoded :
    Internal.vectorLoop code 101 { bytes := artifactBytes, pos := 6758, limit := 30726 } =
      .ok (Cache.raw.codes.drop 52, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code52_decoded codes_tail53_decoded

theorem codes_tail51_decoded :
    Internal.vectorLoop code 102 { bytes := artifactBytes, pos := 6699, limit := 30726 } =
      .ok (Cache.raw.codes.drop 51, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code51_decoded codes_tail52_decoded

theorem codes_tail50_decoded :
    Internal.vectorLoop code 103 { bytes := artifactBytes, pos := 6636, limit := 30726 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code50_decoded codes_tail51_decoded

theorem codes_tail49_decoded :
    Internal.vectorLoop code 104 { bytes := artifactBytes, pos := 6550, limit := 30726 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50_decoded

theorem codes_tail48_decoded :
    Internal.vectorLoop code 105 { bytes := artifactBytes, pos := 6519, limit := 30726 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49_decoded

theorem codes_tail47_decoded :
    Internal.vectorLoop code 106 { bytes := artifactBytes, pos := 6310, limit := 30726 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48_decoded

theorem codes_tail46_decoded :
    Internal.vectorLoop code 107 { bytes := artifactBytes, pos := 5976, limit := 30726 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47_decoded

theorem codes_tail45_decoded :
    Internal.vectorLoop code 108 { bytes := artifactBytes, pos := 5899, limit := 30726 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46_decoded

theorem codes_tail44_decoded :
    Internal.vectorLoop code 109 { bytes := artifactBytes, pos := 5870, limit := 30726 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45_decoded

theorem codes_tail43_decoded :
    Internal.vectorLoop code 110 { bytes := artifactBytes, pos := 5763, limit := 30726 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44_decoded

theorem codes_tail42_decoded :
    Internal.vectorLoop code 111 { bytes := artifactBytes, pos := 5752, limit := 30726 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43_decoded

theorem codes_tail41_decoded :
    Internal.vectorLoop code 112 { bytes := artifactBytes, pos := 5741, limit := 30726 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42_decoded

theorem codes_tail40_decoded :
    Internal.vectorLoop code 113 { bytes := artifactBytes, pos := 5730, limit := 30726 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41_decoded

theorem codes_tail39_decoded :
    Internal.vectorLoop code 114 { bytes := artifactBytes, pos := 5719, limit := 30726 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40_decoded

theorem codes_tail38_decoded :
    Internal.vectorLoop code 115 { bytes := artifactBytes, pos := 5453, limit := 30726 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39_decoded

theorem codes_tail37_decoded :
    Internal.vectorLoop code 116 { bytes := artifactBytes, pos := 5334, limit := 30726 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38_decoded

theorem codes_tail36_decoded :
    Internal.vectorLoop code 117 { bytes := artifactBytes, pos := 5223, limit := 30726 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37_decoded

theorem codes_tail35_decoded :
    Internal.vectorLoop code 118 { bytes := artifactBytes, pos := 5011, limit := 30726 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36_decoded

theorem codes_tail34_decoded :
    Internal.vectorLoop code 119 { bytes := artifactBytes, pos := 4877, limit := 30726 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35_decoded

theorem codes_tail33_decoded :
    Internal.vectorLoop code 120 { bytes := artifactBytes, pos := 4758, limit := 30726 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34_decoded

theorem codes_tail32_decoded :
    Internal.vectorLoop code 121 { bytes := artifactBytes, pos := 4646, limit := 30726 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33_decoded

theorem codes_tail31_decoded :
    Internal.vectorLoop code 122 { bytes := artifactBytes, pos := 4295, limit := 30726 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32_decoded

theorem codes_tail30_decoded :
    Internal.vectorLoop code 123 { bytes := artifactBytes, pos := 4183, limit := 30726 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31_decoded

theorem codes_tail29_decoded :
    Internal.vectorLoop code 124 { bytes := artifactBytes, pos := 4071, limit := 30726 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30_decoded

theorem codes_tail28_decoded :
    Internal.vectorLoop code 125 { bytes := artifactBytes, pos := 3941, limit := 30726 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29_decoded

theorem codes_tail27_decoded :
    Internal.vectorLoop code 126 { bytes := artifactBytes, pos := 3814, limit := 30726 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28_decoded

theorem codes_tail26_decoded :
    Internal.vectorLoop code 127 { bytes := artifactBytes, pos := 3758, limit := 30726 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27_decoded

theorem codes_tail25_decoded :
    Internal.vectorLoop code 128 { bytes := artifactBytes, pos := 3689, limit := 30726 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26_decoded

theorem codes_tail24_decoded :
    Internal.vectorLoop code 129 { bytes := artifactBytes, pos := 3620, limit := 30726 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25_decoded

theorem codes_tail23_decoded :
    Internal.vectorLoop code 130 { bytes := artifactBytes, pos := 3537, limit := 30726 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24_decoded

theorem codes_tail22_decoded :
    Internal.vectorLoop code 131 { bytes := artifactBytes, pos := 3206, limit := 30726 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23_decoded

theorem codes_tail21_decoded :
    Internal.vectorLoop code 132 { bytes := artifactBytes, pos := 3070, limit := 30726 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22_decoded

theorem codes_tail20_decoded :
    Internal.vectorLoop code 133 { bytes := artifactBytes, pos := 3002, limit := 30726 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21_decoded

theorem codes_tail19_decoded :
    Internal.vectorLoop code 134 { bytes := artifactBytes, pos := 2886, limit := 30726 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 135 { bytes := artifactBytes, pos := 2811, limit := 30726 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 136 { bytes := artifactBytes, pos := 2752, limit := 30726 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 137 { bytes := artifactBytes, pos := 2720, limit := 30726 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 138 { bytes := artifactBytes, pos := 2638, limit := 30726 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 139 { bytes := artifactBytes, pos := 2539, limit := 30726 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 140 { bytes := artifactBytes, pos := 2493, limit := 30726 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 141 { bytes := artifactBytes, pos := 2471, limit := 30726 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 142 { bytes := artifactBytes, pos := 2434, limit := 30726 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 143 { bytes := artifactBytes, pos := 2411, limit := 30726 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 144 { bytes := artifactBytes, pos := 2369, limit := 30726 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 145 { bytes := artifactBytes, pos := 2241, limit := 30726 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 146 { bytes := artifactBytes, pos := 2204, limit := 30726 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 147 { bytes := artifactBytes, pos := 2181, limit := 30726 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 148 { bytes := artifactBytes, pos := 2139, limit := 30726 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 149 { bytes := artifactBytes, pos := 2030, limit := 30726 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded

theorem codes_tail3_decoded :
    Internal.vectorLoop code 150 { bytes := artifactBytes, pos := 2013, limit := 30726 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 151 { bytes := artifactBytes, pos := 2002, limit := 30726 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 152 { bytes := artifactBytes, pos := 1991, limit := 30726 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 153 { bytes := artifactBytes, pos := 1972, limit := 30726 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 1970, limit := 30726 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  refine vector_eq_of_parts (length := 153)
    (itemsStart := { bytes := artifactBytes, pos := 1972, limit := 30726 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

#print axioms codes_vector_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 1967, limit := 30726 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  refine sized_eq_of_parts (size := 28756)
    (payload := { bytes := artifactBytes, pos := 1970, limit := 30726 }) (finish := { bytes := artifactBytes, pos := 30726, limit := 30726 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded


end Project.EulerReconstructed.Artifact
