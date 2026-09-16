import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes0To7
import Project.EulerCertificate.ArtifactCodes8To15
import Project.EulerCertificate.ArtifactCodes16To23
import Project.EulerCertificate.ArtifactCodes24To31
import Project.EulerCertificate.ArtifactCodes32To39
import Project.EulerCertificate.ArtifactCodes40To47
import Project.EulerCertificate.ArtifactCodes48To55
import Project.EulerCertificate.ArtifactCodes56To63
import Project.EulerCertificate.ArtifactCodes64To71
import Project.EulerCertificate.ArtifactCodes72To79
import Project.EulerCertificate.ArtifactCodes80To87
import Project.EulerCertificate.ArtifactCodes88To95
import Project.EulerCertificate.ArtifactCodes96To103
import Project.EulerCertificate.ArtifactCodes104To111
import Project.EulerCertificate.ArtifactCodes112To119
import Project.EulerCertificate.ArtifactCodes120To127
import Project.EulerCertificate.ArtifactCodes128To135
import Project.EulerCertificate.ArtifactCodes136To143
import Project.EulerCertificate.ArtifactCodes144To151
import Project.EulerCertificate.ArtifactCodes152To159
import Project.EulerCertificate.ArtifactCodes160To167
import Project.EulerCertificate.ArtifactCodes168To175
import Project.EulerCertificate.ArtifactCodes176To183
import Project.EulerCertificate.ArtifactCodes184To191
import Project.EulerCertificate.ArtifactCodes192To194

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail195_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 45644, limit := 45644 } =
      .ok (Cache.raw.codes.drop 195, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by rfl

theorem codes_tail194_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 45289, limit := 45644 } =
      .ok (Cache.raw.codes.drop 194, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code194_decoded codes_tail195_decoded

theorem codes_tail193_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 45208, limit := 45644 } =
      .ok (Cache.raw.codes.drop 193, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code193_decoded codes_tail194_decoded

theorem codes_tail192_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 45180, limit := 45644 } =
      .ok (Cache.raw.codes.drop 192, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code192_decoded codes_tail193_decoded

theorem codes_tail191_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 44813, limit := 45644 } =
      .ok (Cache.raw.codes.drop 191, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code191_decoded codes_tail192_decoded

theorem codes_tail190_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 44646, limit := 45644 } =
      .ok (Cache.raw.codes.drop 190, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code190_decoded codes_tail191_decoded

theorem codes_tail189_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 42850, limit := 45644 } =
      .ok (Cache.raw.codes.drop 189, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code189_decoded codes_tail190_decoded

theorem codes_tail188_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 42839, limit := 45644 } =
      .ok (Cache.raw.codes.drop 188, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code188_decoded codes_tail189_decoded

theorem codes_tail187_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 42828, limit := 45644 } =
      .ok (Cache.raw.codes.drop 187, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code187_decoded codes_tail188_decoded

theorem codes_tail186_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 42751, limit := 45644 } =
      .ok (Cache.raw.codes.drop 186, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code186_decoded codes_tail187_decoded

theorem codes_tail185_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 42734, limit := 45644 } =
      .ok (Cache.raw.codes.drop 185, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code185_decoded codes_tail186_decoded

theorem codes_tail184_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 41455, limit := 45644 } =
      .ok (Cache.raw.codes.drop 184, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code184_decoded codes_tail185_decoded

theorem codes_tail183_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 41438, limit := 45644 } =
      .ok (Cache.raw.codes.drop 183, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code183_decoded codes_tail184_decoded

theorem codes_tail182_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 41427, limit := 45644 } =
      .ok (Cache.raw.codes.drop 182, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code182_decoded codes_tail183_decoded

theorem codes_tail181_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 41350, limit := 45644 } =
      .ok (Cache.raw.codes.drop 181, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code181_decoded codes_tail182_decoded

theorem codes_tail180_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 41339, limit := 45644 } =
      .ok (Cache.raw.codes.drop 180, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code180_decoded codes_tail181_decoded


theorem codes_tail179_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 39739, limit := 45644 } =
      .ok (Cache.raw.codes.drop 179, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code179_decoded codes_tail180_decoded

theorem codes_tail178_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 39662, limit := 45644 } =
      .ok (Cache.raw.codes.drop 178, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code178_decoded codes_tail179_decoded

theorem codes_tail177_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 39645, limit := 45644 } =
      .ok (Cache.raw.codes.drop 177, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code177_decoded codes_tail178_decoded

theorem codes_tail176_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 39098, limit := 45644 } =
      .ok (Cache.raw.codes.drop 176, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code176_decoded codes_tail177_decoded

theorem codes_tail175_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 38418, limit := 45644 } =
      .ok (Cache.raw.codes.drop 175, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code175_decoded codes_tail176_decoded

theorem codes_tail174_decoded :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 38160, limit := 45644 } =
      .ok (Cache.raw.codes.drop 174, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code174_decoded codes_tail175_decoded

theorem codes_tail173_decoded :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 37242, limit := 45644 } =
      .ok (Cache.raw.codes.drop 173, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code173_decoded codes_tail174_decoded

theorem codes_tail172_decoded :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 36759, limit := 45644 } =
      .ok (Cache.raw.codes.drop 172, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code172_decoded codes_tail173_decoded

theorem codes_tail171_decoded :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 36453, limit := 45644 } =
      .ok (Cache.raw.codes.drop 171, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code171_decoded codes_tail172_decoded

theorem codes_tail170_decoded :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 35425, limit := 45644 } =
      .ok (Cache.raw.codes.drop 170, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code170_decoded codes_tail171_decoded

theorem codes_tail169_decoded :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 34897, limit := 45644 } =
      .ok (Cache.raw.codes.drop 169, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code169_decoded codes_tail170_decoded

theorem codes_tail168_decoded :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 34572, limit := 45644 } =
      .ok (Cache.raw.codes.drop 168, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code168_decoded codes_tail169_decoded

theorem codes_tail167_decoded :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 34110, limit := 45644 } =
      .ok (Cache.raw.codes.drop 167, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code167_decoded codes_tail168_decoded

theorem codes_tail166_decoded :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 33709, limit := 45644 } =
      .ok (Cache.raw.codes.drop 166, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code166_decoded codes_tail167_decoded

theorem codes_tail165_decoded :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 33518, limit := 45644 } =
      .ok (Cache.raw.codes.drop 165, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code165_decoded codes_tail166_decoded

theorem codes_tail164_decoded :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 33252, limit := 45644 } =
      .ok (Cache.raw.codes.drop 164, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code164_decoded codes_tail165_decoded


theorem codes_tail163_decoded :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 33105, limit := 45644 } =
      .ok (Cache.raw.codes.drop 163, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code163_decoded codes_tail164_decoded

theorem codes_tail162_decoded :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 32488, limit := 45644 } =
      .ok (Cache.raw.codes.drop 162, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code162_decoded codes_tail163_decoded

theorem codes_tail161_decoded :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 32241, limit := 45644 } =
      .ok (Cache.raw.codes.drop 161, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code161_decoded codes_tail162_decoded

theorem codes_tail160_decoded :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 32230, limit := 45644 } =
      .ok (Cache.raw.codes.drop 160, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code160_decoded codes_tail161_decoded

theorem codes_tail159_decoded :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 31387, limit := 45644 } =
      .ok (Cache.raw.codes.drop 159, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code159_decoded codes_tail160_decoded

theorem codes_tail158_decoded :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 30920, limit := 45644 } =
      .ok (Cache.raw.codes.drop 158, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code158_decoded codes_tail159_decoded

theorem codes_tail157_decoded :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 30909, limit := 45644 } =
      .ok (Cache.raw.codes.drop 157, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code157_decoded codes_tail158_decoded

theorem codes_tail156_decoded :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 30898, limit := 45644 } =
      .ok (Cache.raw.codes.drop 156, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code156_decoded codes_tail157_decoded

theorem codes_tail155_decoded :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 30887, limit := 45644 } =
      .ok (Cache.raw.codes.drop 155, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code155_decoded codes_tail156_decoded

theorem codes_tail154_decoded :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 30876, limit := 45644 } =
      .ok (Cache.raw.codes.drop 154, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code154_decoded codes_tail155_decoded

theorem codes_tail153_decoded :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 30865, limit := 45644 } =
      .ok (Cache.raw.codes.drop 153, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code153_decoded codes_tail154_decoded

theorem codes_tail152_decoded :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 30854, limit := 45644 } =
      .ok (Cache.raw.codes.drop 152, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code152_decoded codes_tail153_decoded

theorem codes_tail151_decoded :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 30825, limit := 45644 } =
      .ok (Cache.raw.codes.drop 151, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code151_decoded codes_tail152_decoded

theorem codes_tail150_decoded :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 30796, limit := 45644 } =
      .ok (Cache.raw.codes.drop 150, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code150_decoded codes_tail151_decoded

theorem codes_tail149_decoded :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 30767, limit := 45644 } =
      .ok (Cache.raw.codes.drop 149, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code149_decoded codes_tail150_decoded

theorem codes_tail148_decoded :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 30738, limit := 45644 } =
      .ok (Cache.raw.codes.drop 148, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code148_decoded codes_tail149_decoded


theorem codes_tail147_decoded :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 30709, limit := 45644 } =
      .ok (Cache.raw.codes.drop 147, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code147_decoded codes_tail148_decoded

theorem codes_tail146_decoded :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 29908, limit := 45644 } =
      .ok (Cache.raw.codes.drop 146, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code146_decoded codes_tail147_decoded

theorem codes_tail145_decoded :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 29879, limit := 45644 } =
      .ok (Cache.raw.codes.drop 145, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code145_decoded codes_tail146_decoded

theorem codes_tail144_decoded :
    Internal.vectorLoop code 51 { bytes := artifactBytes, pos := 29850, limit := 45644 } =
      .ok (Cache.raw.codes.drop 144, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code144_decoded codes_tail145_decoded

theorem codes_tail143_decoded :
    Internal.vectorLoop code 52 { bytes := artifactBytes, pos := 29501, limit := 45644 } =
      .ok (Cache.raw.codes.drop 143, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code143_decoded codes_tail144_decoded

theorem codes_tail142_decoded :
    Internal.vectorLoop code 53 { bytes := artifactBytes, pos := 28615, limit := 45644 } =
      .ok (Cache.raw.codes.drop 142, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code142_decoded codes_tail143_decoded

theorem codes_tail141_decoded :
    Internal.vectorLoop code 54 { bytes := artifactBytes, pos := 28562, limit := 45644 } =
      .ok (Cache.raw.codes.drop 141, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code141_decoded codes_tail142_decoded

theorem codes_tail140_decoded :
    Internal.vectorLoop code 55 { bytes := artifactBytes, pos := 28551, limit := 45644 } =
      .ok (Cache.raw.codes.drop 140, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code140_decoded codes_tail141_decoded

theorem codes_tail139_decoded :
    Internal.vectorLoop code 56 { bytes := artifactBytes, pos := 28540, limit := 45644 } =
      .ok (Cache.raw.codes.drop 139, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code139_decoded codes_tail140_decoded

theorem codes_tail138_decoded :
    Internal.vectorLoop code 57 { bytes := artifactBytes, pos := 28529, limit := 45644 } =
      .ok (Cache.raw.codes.drop 138, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code138_decoded codes_tail139_decoded

theorem codes_tail137_decoded :
    Internal.vectorLoop code 58 { bytes := artifactBytes, pos := 28518, limit := 45644 } =
      .ok (Cache.raw.codes.drop 137, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code137_decoded codes_tail138_decoded

theorem codes_tail136_decoded :
    Internal.vectorLoop code 59 { bytes := artifactBytes, pos := 28470, limit := 45644 } =
      .ok (Cache.raw.codes.drop 136, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code136_decoded codes_tail137_decoded

theorem codes_tail135_decoded :
    Internal.vectorLoop code 60 { bytes := artifactBytes, pos := 28226, limit := 45644 } =
      .ok (Cache.raw.codes.drop 135, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code135_decoded codes_tail136_decoded

theorem codes_tail134_decoded :
    Internal.vectorLoop code 61 { bytes := artifactBytes, pos := 28215, limit := 45644 } =
      .ok (Cache.raw.codes.drop 134, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code134_decoded codes_tail135_decoded

theorem codes_tail133_decoded :
    Internal.vectorLoop code 62 { bytes := artifactBytes, pos := 28204, limit := 45644 } =
      .ok (Cache.raw.codes.drop 133, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code133_decoded codes_tail134_decoded

theorem codes_tail132_decoded :
    Internal.vectorLoop code 63 { bytes := artifactBytes, pos := 27545, limit := 45644 } =
      .ok (Cache.raw.codes.drop 132, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code132_decoded codes_tail133_decoded


theorem codes_tail131_decoded :
    Internal.vectorLoop code 64 { bytes := artifactBytes, pos := 27504, limit := 45644 } =
      .ok (Cache.raw.codes.drop 131, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code131_decoded codes_tail132_decoded

theorem codes_tail130_decoded :
    Internal.vectorLoop code 65 { bytes := artifactBytes, pos := 27493, limit := 45644 } =
      .ok (Cache.raw.codes.drop 130, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code130_decoded codes_tail131_decoded

theorem codes_tail129_decoded :
    Internal.vectorLoop code 66 { bytes := artifactBytes, pos := 27482, limit := 45644 } =
      .ok (Cache.raw.codes.drop 129, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code129_decoded codes_tail130_decoded

theorem codes_tail128_decoded :
    Internal.vectorLoop code 67 { bytes := artifactBytes, pos := 27471, limit := 45644 } =
      .ok (Cache.raw.codes.drop 128, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code128_decoded codes_tail129_decoded

theorem codes_tail127_decoded :
    Internal.vectorLoop code 68 { bytes := artifactBytes, pos := 27460, limit := 45644 } =
      .ok (Cache.raw.codes.drop 127, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code127_decoded codes_tail128_decoded

theorem codes_tail126_decoded :
    Internal.vectorLoop code 69 { bytes := artifactBytes, pos := 27449, limit := 45644 } =
      .ok (Cache.raw.codes.drop 126, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code126_decoded codes_tail127_decoded

theorem codes_tail125_decoded :
    Internal.vectorLoop code 70 { bytes := artifactBytes, pos := 27438, limit := 45644 } =
      .ok (Cache.raw.codes.drop 125, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code125_decoded codes_tail126_decoded

theorem codes_tail124_decoded :
    Internal.vectorLoop code 71 { bytes := artifactBytes, pos := 27385, limit := 45644 } =
      .ok (Cache.raw.codes.drop 124, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code124_decoded codes_tail125_decoded

theorem codes_tail123_decoded :
    Internal.vectorLoop code 72 { bytes := artifactBytes, pos := 27023, limit := 45644 } =
      .ok (Cache.raw.codes.drop 123, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code123_decoded codes_tail124_decoded

theorem codes_tail122_decoded :
    Internal.vectorLoop code 73 { bytes := artifactBytes, pos := 27006, limit := 45644 } =
      .ok (Cache.raw.codes.drop 122, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code122_decoded codes_tail123_decoded

theorem codes_tail121_decoded :
    Internal.vectorLoop code 74 { bytes := artifactBytes, pos := 26969, limit := 45644 } =
      .ok (Cache.raw.codes.drop 121, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code121_decoded codes_tail122_decoded

theorem codes_tail120_decoded :
    Internal.vectorLoop code 75 { bytes := artifactBytes, pos := 26946, limit := 45644 } =
      .ok (Cache.raw.codes.drop 120, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code120_decoded codes_tail121_decoded

theorem codes_tail119_decoded :
    Internal.vectorLoop code 76 { bytes := artifactBytes, pos := 26904, limit := 45644 } =
      .ok (Cache.raw.codes.drop 119, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code119_decoded codes_tail120_decoded

theorem codes_tail118_decoded :
    Internal.vectorLoop code 77 { bytes := artifactBytes, pos := 26893, limit := 45644 } =
      .ok (Cache.raw.codes.drop 118, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code118_decoded codes_tail119_decoded

theorem codes_tail117_decoded :
    Internal.vectorLoop code 78 { bytes := artifactBytes, pos := 26225, limit := 45644 } =
      .ok (Cache.raw.codes.drop 117, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code117_decoded codes_tail118_decoded

theorem codes_tail116_decoded :
    Internal.vectorLoop code 79 { bytes := artifactBytes, pos := 25680, limit := 45644 } =
      .ok (Cache.raw.codes.drop 116, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code116_decoded codes_tail117_decoded


theorem codes_tail115_decoded :
    Internal.vectorLoop code 80 { bytes := artifactBytes, pos := 25651, limit := 45644 } =
      .ok (Cache.raw.codes.drop 115, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code115_decoded codes_tail116_decoded

theorem codes_tail114_decoded :
    Internal.vectorLoop code 81 { bytes := artifactBytes, pos := 25177, limit := 45644 } =
      .ok (Cache.raw.codes.drop 114, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code114_decoded codes_tail115_decoded

theorem codes_tail113_decoded :
    Internal.vectorLoop code 82 { bytes := artifactBytes, pos := 25166, limit := 45644 } =
      .ok (Cache.raw.codes.drop 113, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code113_decoded codes_tail114_decoded

theorem codes_tail112_decoded :
    Internal.vectorLoop code 83 { bytes := artifactBytes, pos := 24687, limit := 45644 } =
      .ok (Cache.raw.codes.drop 112, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code112_decoded codes_tail113_decoded

theorem codes_tail111_decoded :
    Internal.vectorLoop code 84 { bytes := artifactBytes, pos := 24602, limit := 45644 } =
      .ok (Cache.raw.codes.drop 111, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code111_decoded codes_tail112_decoded

theorem codes_tail110_decoded :
    Internal.vectorLoop code 85 { bytes := artifactBytes, pos := 24549, limit := 45644 } =
      .ok (Cache.raw.codes.drop 110, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code110_decoded codes_tail111_decoded

theorem codes_tail109_decoded :
    Internal.vectorLoop code 86 { bytes := artifactBytes, pos := 24496, limit := 45644 } =
      .ok (Cache.raw.codes.drop 109, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code109_decoded codes_tail110_decoded

theorem codes_tail108_decoded :
    Internal.vectorLoop code 87 { bytes := artifactBytes, pos := 24431, limit := 45644 } =
      .ok (Cache.raw.codes.drop 108, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code108_decoded codes_tail109_decoded

theorem codes_tail107_decoded :
    Internal.vectorLoop code 88 { bytes := artifactBytes, pos := 24420, limit := 45644 } =
      .ok (Cache.raw.codes.drop 107, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code107_decoded codes_tail108_decoded

theorem codes_tail106_decoded :
    Internal.vectorLoop code 89 { bytes := artifactBytes, pos := 24053, limit := 45644 } =
      .ok (Cache.raw.codes.drop 106, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code106_decoded codes_tail107_decoded

theorem codes_tail105_decoded :
    Internal.vectorLoop code 90 { bytes := artifactBytes, pos := 24008, limit := 45644 } =
      .ok (Cache.raw.codes.drop 105, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code105_decoded codes_tail106_decoded

theorem codes_tail104_decoded :
    Internal.vectorLoop code 91 { bytes := artifactBytes, pos := 23979, limit := 45644 } =
      .ok (Cache.raw.codes.drop 104, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code104_decoded codes_tail105_decoded

theorem codes_tail103_decoded :
    Internal.vectorLoop code 92 { bytes := artifactBytes, pos := 23886, limit := 45644 } =
      .ok (Cache.raw.codes.drop 103, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code103_decoded codes_tail104_decoded

theorem codes_tail102_decoded :
    Internal.vectorLoop code 93 { bytes := artifactBytes, pos := 23778, limit := 45644 } =
      .ok (Cache.raw.codes.drop 102, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code102_decoded codes_tail103_decoded

theorem codes_tail101_decoded :
    Internal.vectorLoop code 94 { bytes := artifactBytes, pos := 23695, limit := 45644 } =
      .ok (Cache.raw.codes.drop 101, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code101_decoded codes_tail102_decoded

theorem codes_tail100_decoded :
    Internal.vectorLoop code 95 { bytes := artifactBytes, pos := 23642, limit := 45644 } =
      .ok (Cache.raw.codes.drop 100, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code100_decoded codes_tail101_decoded


theorem codes_tail99_decoded :
    Internal.vectorLoop code 96 { bytes := artifactBytes, pos := 23603, limit := 45644 } =
      .ok (Cache.raw.codes.drop 99, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code99_decoded codes_tail100_decoded

theorem codes_tail98_decoded :
    Internal.vectorLoop code 97 { bytes := artifactBytes, pos := 21945, limit := 45644 } =
      .ok (Cache.raw.codes.drop 98, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code98_decoded codes_tail99_decoded

theorem codes_tail97_decoded :
    Internal.vectorLoop code 98 { bytes := artifactBytes, pos := 21879, limit := 45644 } =
      .ok (Cache.raw.codes.drop 97, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code97_decoded codes_tail98_decoded

theorem codes_tail96_decoded :
    Internal.vectorLoop code 99 { bytes := artifactBytes, pos := 21644, limit := 45644 } =
      .ok (Cache.raw.codes.drop 96, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code96_decoded codes_tail97_decoded

theorem codes_tail95_decoded :
    Internal.vectorLoop code 100 { bytes := artifactBytes, pos := 21501, limit := 45644 } =
      .ok (Cache.raw.codes.drop 95, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code95_decoded codes_tail96_decoded

theorem codes_tail94_decoded :
    Internal.vectorLoop code 101 { bytes := artifactBytes, pos := 21207, limit := 45644 } =
      .ok (Cache.raw.codes.drop 94, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code94_decoded codes_tail95_decoded

theorem codes_tail93_decoded :
    Internal.vectorLoop code 102 { bytes := artifactBytes, pos := 21148, limit := 45644 } =
      .ok (Cache.raw.codes.drop 93, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code93_decoded codes_tail94_decoded

theorem codes_tail92_decoded :
    Internal.vectorLoop code 103 { bytes := artifactBytes, pos := 21085, limit := 45644 } =
      .ok (Cache.raw.codes.drop 92, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code92_decoded codes_tail93_decoded

theorem codes_tail91_decoded :
    Internal.vectorLoop code 104 { bytes := artifactBytes, pos := 20999, limit := 45644 } =
      .ok (Cache.raw.codes.drop 91, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code91_decoded codes_tail92_decoded

theorem codes_tail90_decoded :
    Internal.vectorLoop code 105 { bytes := artifactBytes, pos := 20968, limit := 45644 } =
      .ok (Cache.raw.codes.drop 90, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code90_decoded codes_tail91_decoded

theorem codes_tail89_decoded :
    Internal.vectorLoop code 106 { bytes := artifactBytes, pos := 20634, limit := 45644 } =
      .ok (Cache.raw.codes.drop 89, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code89_decoded codes_tail90_decoded

theorem codes_tail88_decoded :
    Internal.vectorLoop code 107 { bytes := artifactBytes, pos := 20557, limit := 45644 } =
      .ok (Cache.raw.codes.drop 88, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code88_decoded codes_tail89_decoded

theorem codes_tail87_decoded :
    Internal.vectorLoop code 108 { bytes := artifactBytes, pos := 20450, limit := 45644 } =
      .ok (Cache.raw.codes.drop 87, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code87_decoded codes_tail88_decoded

theorem codes_tail86_decoded :
    Internal.vectorLoop code 109 { bytes := artifactBytes, pos := 20184, limit := 45644 } =
      .ok (Cache.raw.codes.drop 86, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code86_decoded codes_tail87_decoded

theorem codes_tail85_decoded :
    Internal.vectorLoop code 110 { bytes := artifactBytes, pos := 20065, limit := 45644 } =
      .ok (Cache.raw.codes.drop 85, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code85_decoded codes_tail86_decoded

theorem codes_tail84_decoded :
    Internal.vectorLoop code 111 { bytes := artifactBytes, pos := 19954, limit := 45644 } =
      .ok (Cache.raw.codes.drop 84, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code84_decoded codes_tail85_decoded


theorem codes_tail83_decoded :
    Internal.vectorLoop code 112 { bytes := artifactBytes, pos := 19742, limit := 45644 } =
      .ok (Cache.raw.codes.drop 83, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code83_decoded codes_tail84_decoded

theorem codes_tail82_decoded :
    Internal.vectorLoop code 113 { bytes := artifactBytes, pos := 19608, limit := 45644 } =
      .ok (Cache.raw.codes.drop 82, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code82_decoded codes_tail83_decoded

theorem codes_tail81_decoded :
    Internal.vectorLoop code 114 { bytes := artifactBytes, pos := 19489, limit := 45644 } =
      .ok (Cache.raw.codes.drop 81, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code81_decoded codes_tail82_decoded

theorem codes_tail80_decoded :
    Internal.vectorLoop code 115 { bytes := artifactBytes, pos := 19377, limit := 45644 } =
      .ok (Cache.raw.codes.drop 80, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code80_decoded codes_tail81_decoded

theorem codes_tail79_decoded :
    Internal.vectorLoop code 116 { bytes := artifactBytes, pos := 19026, limit := 45644 } =
      .ok (Cache.raw.codes.drop 79, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code79_decoded codes_tail80_decoded

theorem codes_tail78_decoded :
    Internal.vectorLoop code 117 { bytes := artifactBytes, pos := 18914, limit := 45644 } =
      .ok (Cache.raw.codes.drop 78, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code78_decoded codes_tail79_decoded

theorem codes_tail77_decoded :
    Internal.vectorLoop code 118 { bytes := artifactBytes, pos := 18805, limit := 45644 } =
      .ok (Cache.raw.codes.drop 77, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code77_decoded codes_tail78_decoded

theorem codes_tail76_decoded :
    Internal.vectorLoop code 119 { bytes := artifactBytes, pos := 18786, limit := 45644 } =
      .ok (Cache.raw.codes.drop 76, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code76_decoded codes_tail77_decoded

theorem codes_tail75_decoded :
    Internal.vectorLoop code 120 { bytes := artifactBytes, pos := 18448, limit := 45644 } =
      .ok (Cache.raw.codes.drop 75, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code75_decoded codes_tail76_decoded

theorem codes_tail74_decoded :
    Internal.vectorLoop code 121 { bytes := artifactBytes, pos := 17740, limit := 45644 } =
      .ok (Cache.raw.codes.drop 74, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code74_decoded codes_tail75_decoded

theorem codes_tail73_decoded :
    Internal.vectorLoop code 122 { bytes := artifactBytes, pos := 17442, limit := 45644 } =
      .ok (Cache.raw.codes.drop 73, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code73_decoded codes_tail74_decoded

theorem codes_tail72_decoded :
    Internal.vectorLoop code 123 { bytes := artifactBytes, pos := 17260, limit := 45644 } =
      .ok (Cache.raw.codes.drop 72, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code72_decoded codes_tail73_decoded

theorem codes_tail71_decoded :
    Internal.vectorLoop code 124 { bytes := artifactBytes, pos := 17186, limit := 45644 } =
      .ok (Cache.raw.codes.drop 71, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code71_decoded codes_tail72_decoded

theorem codes_tail70_decoded :
    Internal.vectorLoop code 125 { bytes := artifactBytes, pos := 16884, limit := 45644 } =
      .ok (Cache.raw.codes.drop 70, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code70_decoded codes_tail71_decoded

theorem codes_tail69_decoded :
    Internal.vectorLoop code 126 { bytes := artifactBytes, pos := 16693, limit := 45644 } =
      .ok (Cache.raw.codes.drop 69, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code69_decoded codes_tail70_decoded

theorem codes_tail68_decoded :
    Internal.vectorLoop code 127 { bytes := artifactBytes, pos := 16581, limit := 45644 } =
      .ok (Cache.raw.codes.drop 68, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code68_decoded codes_tail69_decoded


theorem codes_tail67_decoded :
    Internal.vectorLoop code 128 { bytes := artifactBytes, pos := 16504, limit := 45644 } =
      .ok (Cache.raw.codes.drop 67, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code67_decoded codes_tail68_decoded

theorem codes_tail66_decoded :
    Internal.vectorLoop code 129 { bytes := artifactBytes, pos := 16250, limit := 45644 } =
      .ok (Cache.raw.codes.drop 66, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code66_decoded codes_tail67_decoded

theorem codes_tail65_decoded :
    Internal.vectorLoop code 130 { bytes := artifactBytes, pos := 16064, limit := 45644 } =
      .ok (Cache.raw.codes.drop 65, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code65_decoded codes_tail66_decoded

theorem codes_tail64_decoded :
    Internal.vectorLoop code 131 { bytes := artifactBytes, pos := 15934, limit := 45644 } =
      .ok (Cache.raw.codes.drop 64, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code64_decoded codes_tail65_decoded

theorem codes_tail63_decoded :
    Internal.vectorLoop code 132 { bytes := artifactBytes, pos := 15807, limit := 45644 } =
      .ok (Cache.raw.codes.drop 63, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code63_decoded codes_tail64_decoded

theorem codes_tail62_decoded :
    Internal.vectorLoop code 133 { bytes := artifactBytes, pos := 15790, limit := 45644 } =
      .ok (Cache.raw.codes.drop 62, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code62_decoded codes_tail63_decoded

theorem codes_tail61_decoded :
    Internal.vectorLoop code 134 { bytes := artifactBytes, pos := 15734, limit := 45644 } =
      .ok (Cache.raw.codes.drop 61, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code61_decoded codes_tail62_decoded

theorem codes_tail60_decoded :
    Internal.vectorLoop code 135 { bytes := artifactBytes, pos := 15665, limit := 45644 } =
      .ok (Cache.raw.codes.drop 60, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code60_decoded codes_tail61_decoded

theorem codes_tail59_decoded :
    Internal.vectorLoop code 136 { bytes := artifactBytes, pos := 15596, limit := 45644 } =
      .ok (Cache.raw.codes.drop 59, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code59_decoded codes_tail60_decoded

theorem codes_tail58_decoded :
    Internal.vectorLoop code 137 { bytes := artifactBytes, pos := 15486, limit := 45644 } =
      .ok (Cache.raw.codes.drop 58, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code58_decoded codes_tail59_decoded

theorem codes_tail57_decoded :
    Internal.vectorLoop code 138 { bytes := artifactBytes, pos := 15463, limit := 45644 } =
      .ok (Cache.raw.codes.drop 57, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code57_decoded codes_tail58_decoded

theorem codes_tail56_decoded :
    Internal.vectorLoop code 139 { bytes := artifactBytes, pos := 15452, limit := 45644 } =
      .ok (Cache.raw.codes.drop 56, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code56_decoded codes_tail57_decoded

theorem codes_tail55_decoded :
    Internal.vectorLoop code 140 { bytes := artifactBytes, pos := 15441, limit := 45644 } =
      .ok (Cache.raw.codes.drop 55, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code55_decoded codes_tail56_decoded

theorem codes_tail54_decoded :
    Internal.vectorLoop code 141 { bytes := artifactBytes, pos := 15232, limit := 45644 } =
      .ok (Cache.raw.codes.drop 54, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code54_decoded codes_tail55_decoded

theorem codes_tail53_decoded :
    Internal.vectorLoop code 142 { bytes := artifactBytes, pos := 14145, limit := 45644 } =
      .ok (Cache.raw.codes.drop 53, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code53_decoded codes_tail54_decoded

theorem codes_tail52_decoded :
    Internal.vectorLoop code 143 { bytes := artifactBytes, pos := 11606, limit := 45644 } =
      .ok (Cache.raw.codes.drop 52, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code52_decoded codes_tail53_decoded


theorem codes_tail51_decoded :
    Internal.vectorLoop code 144 { bytes := artifactBytes, pos := 11595, limit := 45644 } =
      .ok (Cache.raw.codes.drop 51, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code51_decoded codes_tail52_decoded

theorem codes_tail50_decoded :
    Internal.vectorLoop code 145 { bytes := artifactBytes, pos := 10973, limit := 45644 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code50_decoded codes_tail51_decoded

theorem codes_tail49_decoded :
    Internal.vectorLoop code 146 { bytes := artifactBytes, pos := 10962, limit := 45644 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50_decoded

theorem codes_tail48_decoded :
    Internal.vectorLoop code 147 { bytes := artifactBytes, pos := 10951, limit := 45644 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49_decoded

theorem codes_tail47_decoded :
    Internal.vectorLoop code 148 { bytes := artifactBytes, pos := 10110, limit := 45644 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48_decoded

theorem codes_tail46_decoded :
    Internal.vectorLoop code 149 { bytes := artifactBytes, pos := 10057, limit := 45644 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47_decoded

theorem codes_tail45_decoded :
    Internal.vectorLoop code 150 { bytes := artifactBytes, pos := 9974, limit := 45644 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46_decoded

theorem codes_tail44_decoded :
    Internal.vectorLoop code 151 { bytes := artifactBytes, pos := 9643, limit := 45644 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45_decoded

theorem codes_tail43_decoded :
    Internal.vectorLoop code 152 { bytes := artifactBytes, pos := 9507, limit := 45644 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44_decoded

theorem codes_tail42_decoded :
    Internal.vectorLoop code 153 { bytes := artifactBytes, pos := 9439, limit := 45644 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43_decoded

theorem codes_tail41_decoded :
    Internal.vectorLoop code 154 { bytes := artifactBytes, pos := 9323, limit := 45644 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42_decoded

theorem codes_tail40_decoded :
    Internal.vectorLoop code 155 { bytes := artifactBytes, pos := 9248, limit := 45644 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41_decoded

theorem codes_tail39_decoded :
    Internal.vectorLoop code 156 { bytes := artifactBytes, pos := 9189, limit := 45644 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40_decoded

theorem codes_tail38_decoded :
    Internal.vectorLoop code 157 { bytes := artifactBytes, pos := 9157, limit := 45644 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39_decoded

theorem codes_tail37_decoded :
    Internal.vectorLoop code 158 { bytes := artifactBytes, pos := 9075, limit := 45644 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38_decoded

theorem codes_tail36_decoded :
    Internal.vectorLoop code 159 { bytes := artifactBytes, pos := 8976, limit := 45644 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37_decoded


theorem codes_tail35_decoded :
    Internal.vectorLoop code 160 { bytes := artifactBytes, pos := 8930, limit := 45644 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36_decoded

theorem codes_tail34_decoded :
    Internal.vectorLoop code 161 { bytes := artifactBytes, pos := 8908, limit := 45644 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35_decoded

theorem codes_tail33_decoded :
    Internal.vectorLoop code 162 { bytes := artifactBytes, pos := 8871, limit := 45644 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34_decoded

theorem codes_tail32_decoded :
    Internal.vectorLoop code 163 { bytes := artifactBytes, pos := 8848, limit := 45644 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33_decoded

theorem codes_tail31_decoded :
    Internal.vectorLoop code 164 { bytes := artifactBytes, pos := 8806, limit := 45644 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32_decoded

theorem codes_tail30_decoded :
    Internal.vectorLoop code 165 { bytes := artifactBytes, pos := 8678, limit := 45644 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31_decoded

theorem codes_tail29_decoded :
    Internal.vectorLoop code 166 { bytes := artifactBytes, pos := 8641, limit := 45644 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30_decoded

theorem codes_tail28_decoded :
    Internal.vectorLoop code 167 { bytes := artifactBytes, pos := 8618, limit := 45644 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29_decoded

theorem codes_tail27_decoded :
    Internal.vectorLoop code 168 { bytes := artifactBytes, pos := 8576, limit := 45644 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28_decoded

theorem codes_tail26_decoded :
    Internal.vectorLoop code 169 { bytes := artifactBytes, pos := 8198, limit := 45644 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27_decoded

theorem codes_tail25_decoded :
    Internal.vectorLoop code 170 { bytes := artifactBytes, pos := 8187, limit := 45644 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26_decoded

theorem codes_tail24_decoded :
    Internal.vectorLoop code 171 { bytes := artifactBytes, pos := 8176, limit := 45644 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25_decoded

theorem codes_tail23_decoded :
    Internal.vectorLoop code 172 { bytes := artifactBytes, pos := 8165, limit := 45644 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24_decoded

theorem codes_tail22_decoded :
    Internal.vectorLoop code 173 { bytes := artifactBytes, pos := 8086, limit := 45644 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23_decoded

theorem codes_tail21_decoded :
    Internal.vectorLoop code 174 { bytes := artifactBytes, pos := 7999, limit := 45644 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22_decoded

theorem codes_tail20_decoded :
    Internal.vectorLoop code 175 { bytes := artifactBytes, pos := 7912, limit := 45644 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21_decoded


theorem codes_tail19_decoded :
    Internal.vectorLoop code 176 { bytes := artifactBytes, pos := 7817, limit := 45644 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 177 { bytes := artifactBytes, pos := 7718, limit := 45644 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 178 { bytes := artifactBytes, pos := 7605, limit := 45644 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 179 { bytes := artifactBytes, pos := 7438, limit := 45644 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 180 { bytes := artifactBytes, pos := 6086, limit := 45644 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 181 { bytes := artifactBytes, pos := 6063, limit := 45644 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 182 { bytes := artifactBytes, pos := 6040, limit := 45644 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 183 { bytes := artifactBytes, pos := 6017, limit := 45644 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 184 { bytes := artifactBytes, pos := 6006, limit := 45644 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 185 { bytes := artifactBytes, pos := 5995, limit := 45644 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 186 { bytes := artifactBytes, pos := 5972, limit := 45644 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 187 { bytes := artifactBytes, pos := 5961, limit := 45644 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 188 { bytes := artifactBytes, pos := 5884, limit := 45644 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 189 { bytes := artifactBytes, pos := 5867, limit := 45644 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 190 { bytes := artifactBytes, pos := 5856, limit := 45644 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 191 { bytes := artifactBytes, pos := 5845, limit := 45644 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded


theorem codes_tail3_decoded :
    Internal.vectorLoop code 192 { bytes := artifactBytes, pos := 3056, limit := 45644 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 193 { bytes := artifactBytes, pos := 3045, limit := 45644 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 194 { bytes := artifactBytes, pos := 3016, limit := 45644 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 195 { bytes := artifactBytes, pos := 3005, limit := 45644 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 3003, limit := 45644 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  refine vector_eq_of_parts (length := 195)
    (itemsStart := { bytes := artifactBytes, pos := 3005, limit := 45644 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

#print axioms codes_vector_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 3000, limit := 45644 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  refine sized_eq_of_parts (size := 42641)
    (payload := { bytes := artifactBytes, pos := 3003, limit := 45644 }) (finish := { bytes := artifactBytes, pos := 45644, limit := 45644 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.EulerCertificate.Artifact
