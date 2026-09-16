import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItems

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_tail195_decoded :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 2571, limit := 2571 } =
      .ok (Cache.raw.types.drop 195, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by rfl

theorem types_tail194_decoded :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 2567, limit := 2571 } =
      .ok (Cache.raw.types.drop 194, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type194_decoded types_tail195_decoded

theorem types_tail193_decoded :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 2562, limit := 2571 } =
      .ok (Cache.raw.types.drop 193, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type193_decoded types_tail194_decoded

theorem types_tail192_decoded :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 2559, limit := 2571 } =
      .ok (Cache.raw.types.drop 192, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type192_decoded types_tail193_decoded

theorem types_tail191_decoded :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 2554, limit := 2571 } =
      .ok (Cache.raw.types.drop 191, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type191_decoded types_tail192_decoded

theorem types_tail190_decoded :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 2548, limit := 2571 } =
      .ok (Cache.raw.types.drop 190, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type190_decoded types_tail191_decoded

theorem types_tail189_decoded :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 2527, limit := 2571 } =
      .ok (Cache.raw.types.drop 189, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type189_decoded types_tail190_decoded

theorem types_tail188_decoded :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 2507, limit := 2571 } =
      .ok (Cache.raw.types.drop 188, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type188_decoded types_tail189_decoded

theorem types_tail187_decoded :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 2487, limit := 2571 } =
      .ok (Cache.raw.types.drop 187, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type187_decoded types_tail188_decoded

theorem types_tail186_decoded :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 2456, limit := 2571 } =
      .ok (Cache.raw.types.drop 186, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type186_decoded types_tail187_decoded

theorem types_tail185_decoded :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 2435, limit := 2571 } =
      .ok (Cache.raw.types.drop 185, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type185_decoded types_tail186_decoded

theorem types_tail184_decoded :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 2398, limit := 2571 } =
      .ok (Cache.raw.types.drop 184, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type184_decoded types_tail185_decoded

theorem types_tail183_decoded :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 2377, limit := 2571 } =
      .ok (Cache.raw.types.drop 183, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type183_decoded types_tail184_decoded

theorem types_tail182_decoded :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 2357, limit := 2571 } =
      .ok (Cache.raw.types.drop 182, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type182_decoded types_tail183_decoded

theorem types_tail181_decoded :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 2326, limit := 2571 } =
      .ok (Cache.raw.types.drop 181, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type181_decoded types_tail182_decoded

theorem types_tail180_decoded :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 2306, limit := 2571 } =
      .ok (Cache.raw.types.drop 180, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type180_decoded types_tail181_decoded


theorem types_tail179_decoded :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 2279, limit := 2571 } =
      .ok (Cache.raw.types.drop 179, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type179_decoded types_tail180_decoded

theorem types_tail178_decoded :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 2250, limit := 2571 } =
      .ok (Cache.raw.types.drop 178, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type178_decoded types_tail179_decoded

theorem types_tail177_decoded :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 2231, limit := 2571 } =
      .ok (Cache.raw.types.drop 177, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type177_decoded types_tail178_decoded

theorem types_tail176_decoded :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 2207, limit := 2571 } =
      .ok (Cache.raw.types.drop 176, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type176_decoded types_tail177_decoded

theorem types_tail175_decoded :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 2185, limit := 2571 } =
      .ok (Cache.raw.types.drop 175, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type175_decoded types_tail176_decoded

theorem types_tail174_decoded :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 2157, limit := 2571 } =
      .ok (Cache.raw.types.drop 174, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type174_decoded types_tail175_decoded

theorem types_tail173_decoded :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 2137, limit := 2571 } =
      .ok (Cache.raw.types.drop 173, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type173_decoded types_tail174_decoded

theorem types_tail172_decoded :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 2116, limit := 2571 } =
      .ok (Cache.raw.types.drop 172, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type172_decoded types_tail173_decoded

theorem types_tail171_decoded :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 2077, limit := 2571 } =
      .ok (Cache.raw.types.drop 171, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type171_decoded types_tail172_decoded

theorem types_tail170_decoded :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 2055, limit := 2571 } =
      .ok (Cache.raw.types.drop 170, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type170_decoded types_tail171_decoded

theorem types_tail169_decoded :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 2031, limit := 2571 } =
      .ok (Cache.raw.types.drop 169, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type169_decoded types_tail170_decoded

theorem types_tail168_decoded :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 2016, limit := 2571 } =
      .ok (Cache.raw.types.drop 168, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type168_decoded types_tail169_decoded

theorem types_tail167_decoded :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 1997, limit := 2571 } =
      .ok (Cache.raw.types.drop 167, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type167_decoded types_tail168_decoded

theorem types_tail166_decoded :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 1987, limit := 2571 } =
      .ok (Cache.raw.types.drop 166, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type166_decoded types_tail167_decoded

theorem types_tail165_decoded :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 1975, limit := 2571 } =
      .ok (Cache.raw.types.drop 165, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type165_decoded types_tail166_decoded

theorem types_tail164_decoded :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 1965, limit := 2571 } =
      .ok (Cache.raw.types.drop 164, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type164_decoded types_tail165_decoded


theorem types_tail163_decoded :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 1937, limit := 2571 } =
      .ok (Cache.raw.types.drop 163, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type163_decoded types_tail164_decoded

theorem types_tail162_decoded :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 1924, limit := 2571 } =
      .ok (Cache.raw.types.drop 162, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type162_decoded types_tail163_decoded

theorem types_tail161_decoded :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 1918, limit := 2571 } =
      .ok (Cache.raw.types.drop 161, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type161_decoded types_tail162_decoded

theorem types_tail160_decoded :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 1907, limit := 2571 } =
      .ok (Cache.raw.types.drop 160, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type160_decoded types_tail161_decoded

theorem types_tail159_decoded :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 1896, limit := 2571 } =
      .ok (Cache.raw.types.drop 159, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type159_decoded types_tail160_decoded

theorem types_tail158_decoded :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 1873, limit := 2571 } =
      .ok (Cache.raw.types.drop 158, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type158_decoded types_tail159_decoded

theorem types_tail157_decoded :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 1861, limit := 2571 } =
      .ok (Cache.raw.types.drop 157, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type157_decoded types_tail158_decoded

theorem types_tail156_decoded :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 1849, limit := 2571 } =
      .ok (Cache.raw.types.drop 156, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type156_decoded types_tail157_decoded

theorem types_tail155_decoded :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 1837, limit := 2571 } =
      .ok (Cache.raw.types.drop 155, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type155_decoded types_tail156_decoded

theorem types_tail154_decoded :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 1825, limit := 2571 } =
      .ok (Cache.raw.types.drop 154, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type154_decoded types_tail155_decoded

theorem types_tail153_decoded :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 1813, limit := 2571 } =
      .ok (Cache.raw.types.drop 153, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type153_decoded types_tail154_decoded

theorem types_tail152_decoded :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 1801, limit := 2571 } =
      .ok (Cache.raw.types.drop 152, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type152_decoded types_tail153_decoded

theorem types_tail151_decoded :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 1774, limit := 2571 } =
      .ok (Cache.raw.types.drop 151, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type151_decoded types_tail152_decoded

theorem types_tail150_decoded :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 1747, limit := 2571 } =
      .ok (Cache.raw.types.drop 150, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type150_decoded types_tail151_decoded

theorem types_tail149_decoded :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 1720, limit := 2571 } =
      .ok (Cache.raw.types.drop 149, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type149_decoded types_tail150_decoded

theorem types_tail148_decoded :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 1693, limit := 2571 } =
      .ok (Cache.raw.types.drop 148, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type148_decoded types_tail149_decoded


theorem types_tail147_decoded :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 1666, limit := 2571 } =
      .ok (Cache.raw.types.drop 147, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type147_decoded types_tail148_decoded

theorem types_tail146_decoded :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 1633, limit := 2571 } =
      .ok (Cache.raw.types.drop 146, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type146_decoded types_tail147_decoded

theorem types_tail145_decoded :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 1616, limit := 2571 } =
      .ok (Cache.raw.types.drop 145, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type145_decoded types_tail146_decoded

theorem types_tail144_decoded :
    Internal.vectorLoop funcType 51 { bytes := artifactBytes, pos := 1599, limit := 2571 } =
      .ok (Cache.raw.types.drop 144, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type144_decoded types_tail145_decoded

theorem types_tail143_decoded :
    Internal.vectorLoop funcType 52 { bytes := artifactBytes, pos := 1567, limit := 2571 } =
      .ok (Cache.raw.types.drop 143, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type143_decoded types_tail144_decoded

theorem types_tail142_decoded :
    Internal.vectorLoop funcType 53 { bytes := artifactBytes, pos := 1539, limit := 2571 } =
      .ok (Cache.raw.types.drop 142, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type142_decoded types_tail143_decoded

theorem types_tail141_decoded :
    Internal.vectorLoop funcType 54 { bytes := artifactBytes, pos := 1528, limit := 2571 } =
      .ok (Cache.raw.types.drop 141, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type141_decoded types_tail142_decoded

theorem types_tail140_decoded :
    Internal.vectorLoop funcType 55 { bytes := artifactBytes, pos := 1518, limit := 2571 } =
      .ok (Cache.raw.types.drop 140, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type140_decoded types_tail141_decoded

theorem types_tail139_decoded :
    Internal.vectorLoop funcType 56 { bytes := artifactBytes, pos := 1508, limit := 2571 } =
      .ok (Cache.raw.types.drop 139, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type139_decoded types_tail140_decoded

theorem types_tail138_decoded :
    Internal.vectorLoop funcType 57 { bytes := artifactBytes, pos := 1498, limit := 2571 } =
      .ok (Cache.raw.types.drop 138, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type138_decoded types_tail139_decoded

theorem types_tail137_decoded :
    Internal.vectorLoop funcType 58 { bytes := artifactBytes, pos := 1488, limit := 2571 } =
      .ok (Cache.raw.types.drop 137, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type137_decoded types_tail138_decoded

theorem types_tail136_decoded :
    Internal.vectorLoop funcType 59 { bytes := artifactBytes, pos := 1479, limit := 2571 } =
      .ok (Cache.raw.types.drop 136, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type136_decoded types_tail137_decoded

theorem types_tail135_decoded :
    Internal.vectorLoop funcType 60 { bytes := artifactBytes, pos := 1470, limit := 2571 } =
      .ok (Cache.raw.types.drop 135, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type135_decoded types_tail136_decoded

theorem types_tail134_decoded :
    Internal.vectorLoop funcType 61 { bytes := artifactBytes, pos := 1460, limit := 2571 } =
      .ok (Cache.raw.types.drop 134, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type134_decoded types_tail135_decoded

theorem types_tail133_decoded :
    Internal.vectorLoop funcType 62 { bytes := artifactBytes, pos := 1450, limit := 2571 } =
      .ok (Cache.raw.types.drop 133, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type133_decoded types_tail134_decoded

theorem types_tail132_decoded :
    Internal.vectorLoop funcType 63 { bytes := artifactBytes, pos := 1433, limit := 2571 } =
      .ok (Cache.raw.types.drop 132, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type132_decoded types_tail133_decoded


theorem types_tail131_decoded :
    Internal.vectorLoop funcType 64 { bytes := artifactBytes, pos := 1424, limit := 2571 } =
      .ok (Cache.raw.types.drop 131, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type131_decoded types_tail132_decoded

theorem types_tail130_decoded :
    Internal.vectorLoop funcType 65 { bytes := artifactBytes, pos := 1418, limit := 2571 } =
      .ok (Cache.raw.types.drop 130, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type130_decoded types_tail131_decoded

theorem types_tail129_decoded :
    Internal.vectorLoop funcType 66 { bytes := artifactBytes, pos := 1412, limit := 2571 } =
      .ok (Cache.raw.types.drop 129, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type129_decoded types_tail130_decoded

theorem types_tail128_decoded :
    Internal.vectorLoop funcType 67 { bytes := artifactBytes, pos := 1400, limit := 2571 } =
      .ok (Cache.raw.types.drop 128, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type128_decoded types_tail129_decoded

theorem types_tail127_decoded :
    Internal.vectorLoop funcType 68 { bytes := artifactBytes, pos := 1388, limit := 2571 } =
      .ok (Cache.raw.types.drop 127, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type127_decoded types_tail128_decoded

theorem types_tail126_decoded :
    Internal.vectorLoop funcType 69 { bytes := artifactBytes, pos := 1376, limit := 2571 } =
      .ok (Cache.raw.types.drop 126, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type126_decoded types_tail127_decoded

theorem types_tail125_decoded :
    Internal.vectorLoop funcType 70 { bytes := artifactBytes, pos := 1364, limit := 2571 } =
      .ok (Cache.raw.types.drop 125, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type125_decoded types_tail126_decoded

theorem types_tail124_decoded :
    Internal.vectorLoop funcType 71 { bytes := artifactBytes, pos := 1354, limit := 2571 } =
      .ok (Cache.raw.types.drop 124, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type124_decoded types_tail125_decoded

theorem types_tail123_decoded :
    Internal.vectorLoop funcType 72 { bytes := artifactBytes, pos := 1344, limit := 2571 } =
      .ok (Cache.raw.types.drop 123, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type123_decoded types_tail124_decoded

theorem types_tail122_decoded :
    Internal.vectorLoop funcType 73 { bytes := artifactBytes, pos := 1339, limit := 2571 } =
      .ok (Cache.raw.types.drop 122, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type122_decoded types_tail123_decoded

theorem types_tail121_decoded :
    Internal.vectorLoop funcType 74 { bytes := artifactBytes, pos := 1334, limit := 2571 } =
      .ok (Cache.raw.types.drop 121, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type121_decoded types_tail122_decoded

theorem types_tail120_decoded :
    Internal.vectorLoop funcType 75 { bytes := artifactBytes, pos := 1329, limit := 2571 } =
      .ok (Cache.raw.types.drop 120, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type120_decoded types_tail121_decoded

theorem types_tail119_decoded :
    Internal.vectorLoop funcType 76 { bytes := artifactBytes, pos := 1324, limit := 2571 } =
      .ok (Cache.raw.types.drop 119, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type119_decoded types_tail120_decoded

theorem types_tail118_decoded :
    Internal.vectorLoop funcType 77 { bytes := artifactBytes, pos := 1312, limit := 2571 } =
      .ok (Cache.raw.types.drop 118, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type118_decoded types_tail119_decoded

theorem types_tail117_decoded :
    Internal.vectorLoop funcType 78 { bytes := artifactBytes, pos := 1297, limit := 2571 } =
      .ok (Cache.raw.types.drop 117, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type117_decoded types_tail118_decoded

theorem types_tail116_decoded :
    Internal.vectorLoop funcType 79 { bytes := artifactBytes, pos := 1271, limit := 2571 } =
      .ok (Cache.raw.types.drop 116, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type116_decoded types_tail117_decoded


theorem types_tail115_decoded :
    Internal.vectorLoop funcType 80 { bytes := artifactBytes, pos := 1259, limit := 2571 } =
      .ok (Cache.raw.types.drop 115, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type115_decoded types_tail116_decoded

theorem types_tail114_decoded :
    Internal.vectorLoop funcType 81 { bytes := artifactBytes, pos := 1236, limit := 2571 } =
      .ok (Cache.raw.types.drop 114, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type114_decoded types_tail115_decoded

theorem types_tail113_decoded :
    Internal.vectorLoop funcType 82 { bytes := artifactBytes, pos := 1222, limit := 2571 } =
      .ok (Cache.raw.types.drop 113, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type113_decoded types_tail114_decoded

theorem types_tail112_decoded :
    Internal.vectorLoop funcType 83 { bytes := artifactBytes, pos := 1200, limit := 2571 } =
      .ok (Cache.raw.types.drop 112, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type112_decoded types_tail113_decoded

theorem types_tail111_decoded :
    Internal.vectorLoop funcType 84 { bytes := artifactBytes, pos := 1187, limit := 2571 } =
      .ok (Cache.raw.types.drop 111, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type111_decoded types_tail112_decoded

theorem types_tail110_decoded :
    Internal.vectorLoop funcType 85 { bytes := artifactBytes, pos := 1172, limit := 2571 } =
      .ok (Cache.raw.types.drop 110, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type110_decoded types_tail111_decoded

theorem types_tail109_decoded :
    Internal.vectorLoop funcType 86 { bytes := artifactBytes, pos := 1160, limit := 2571 } =
      .ok (Cache.raw.types.drop 109, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type109_decoded types_tail110_decoded

theorem types_tail108_decoded :
    Internal.vectorLoop funcType 87 { bytes := artifactBytes, pos := 1143, limit := 2571 } =
      .ok (Cache.raw.types.drop 108, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type108_decoded types_tail109_decoded

theorem types_tail107_decoded :
    Internal.vectorLoop funcType 88 { bytes := artifactBytes, pos := 1134, limit := 2571 } =
      .ok (Cache.raw.types.drop 107, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type107_decoded types_tail108_decoded

theorem types_tail106_decoded :
    Internal.vectorLoop funcType 89 { bytes := artifactBytes, pos := 1114, limit := 2571 } =
      .ok (Cache.raw.types.drop 106, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type106_decoded types_tail107_decoded

theorem types_tail105_decoded :
    Internal.vectorLoop funcType 90 { bytes := artifactBytes, pos := 1106, limit := 2571 } =
      .ok (Cache.raw.types.drop 105, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type105_decoded types_tail106_decoded

theorem types_tail104_decoded :
    Internal.vectorLoop funcType 91 { bytes := artifactBytes, pos := 1099, limit := 2571 } =
      .ok (Cache.raw.types.drop 104, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type104_decoded types_tail105_decoded

theorem types_tail103_decoded :
    Internal.vectorLoop funcType 92 { bytes := artifactBytes, pos := 1084, limit := 2571 } =
      .ok (Cache.raw.types.drop 103, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type103_decoded types_tail104_decoded

theorem types_tail102_decoded :
    Internal.vectorLoop funcType 93 { bytes := artifactBytes, pos := 1078, limit := 2571 } =
      .ok (Cache.raw.types.drop 102, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type102_decoded types_tail103_decoded

theorem types_tail101_decoded :
    Internal.vectorLoop funcType 94 { bytes := artifactBytes, pos := 1070, limit := 2571 } =
      .ok (Cache.raw.types.drop 101, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type101_decoded types_tail102_decoded

theorem types_tail100_decoded :
    Internal.vectorLoop funcType 95 { bytes := artifactBytes, pos := 1055, limit := 2571 } =
      .ok (Cache.raw.types.drop 100, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type100_decoded types_tail101_decoded


theorem types_tail99_decoded :
    Internal.vectorLoop funcType 96 { bytes := artifactBytes, pos := 1047, limit := 2571 } =
      .ok (Cache.raw.types.drop 99, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type99_decoded types_tail100_decoded

theorem types_tail98_decoded :
    Internal.vectorLoop funcType 97 { bytes := artifactBytes, pos := 1013, limit := 2571 } =
      .ok (Cache.raw.types.drop 98, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type98_decoded types_tail99_decoded

theorem types_tail97_decoded :
    Internal.vectorLoop funcType 98 { bytes := artifactBytes, pos := 1001, limit := 2571 } =
      .ok (Cache.raw.types.drop 97, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type97_decoded types_tail98_decoded

theorem types_tail96_decoded :
    Internal.vectorLoop funcType 99 { bytes := artifactBytes, pos := 993, limit := 2571 } =
      .ok (Cache.raw.types.drop 96, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type96_decoded types_tail97_decoded

theorem types_tail95_decoded :
    Internal.vectorLoop funcType 100 { bytes := artifactBytes, pos := 985, limit := 2571 } =
      .ok (Cache.raw.types.drop 95, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type95_decoded types_tail96_decoded

theorem types_tail94_decoded :
    Internal.vectorLoop funcType 101 { bytes := artifactBytes, pos := 977, limit := 2571 } =
      .ok (Cache.raw.types.drop 94, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type94_decoded types_tail95_decoded

theorem types_tail93_decoded :
    Internal.vectorLoop funcType 102 { bytes := artifactBytes, pos := 971, limit := 2571 } =
      .ok (Cache.raw.types.drop 93, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type93_decoded types_tail94_decoded

theorem types_tail92_decoded :
    Internal.vectorLoop funcType 103 { bytes := artifactBytes, pos := 965, limit := 2571 } =
      .ok (Cache.raw.types.drop 92, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type92_decoded types_tail93_decoded

theorem types_tail91_decoded :
    Internal.vectorLoop funcType 104 { bytes := artifactBytes, pos := 958, limit := 2571 } =
      .ok (Cache.raw.types.drop 91, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type91_decoded types_tail92_decoded

theorem types_tail90_decoded :
    Internal.vectorLoop funcType 105 { bytes := artifactBytes, pos := 953, limit := 2571 } =
      .ok (Cache.raw.types.drop 90, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type90_decoded types_tail91_decoded

theorem types_tail89_decoded :
    Internal.vectorLoop funcType 106 { bytes := artifactBytes, pos := 946, limit := 2571 } =
      .ok (Cache.raw.types.drop 89, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type89_decoded types_tail90_decoded

theorem types_tail88_decoded :
    Internal.vectorLoop funcType 107 { bytes := artifactBytes, pos := 932, limit := 2571 } =
      .ok (Cache.raw.types.drop 88, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type88_decoded types_tail89_decoded

theorem types_tail87_decoded :
    Internal.vectorLoop funcType 108 { bytes := artifactBytes, pos := 923, limit := 2571 } =
      .ok (Cache.raw.types.drop 87, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type87_decoded types_tail88_decoded

theorem types_tail86_decoded :
    Internal.vectorLoop funcType 109 { bytes := artifactBytes, pos := 914, limit := 2571 } =
      .ok (Cache.raw.types.drop 86, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type86_decoded types_tail87_decoded

theorem types_tail85_decoded :
    Internal.vectorLoop funcType 110 { bytes := artifactBytes, pos := 905, limit := 2571 } =
      .ok (Cache.raw.types.drop 85, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type85_decoded types_tail86_decoded

theorem types_tail84_decoded :
    Internal.vectorLoop funcType 111 { bytes := artifactBytes, pos := 898, limit := 2571 } =
      .ok (Cache.raw.types.drop 84, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type84_decoded types_tail85_decoded


theorem types_tail83_decoded :
    Internal.vectorLoop funcType 112 { bytes := artifactBytes, pos := 889, limit := 2571 } =
      .ok (Cache.raw.types.drop 83, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type83_decoded types_tail84_decoded

theorem types_tail82_decoded :
    Internal.vectorLoop funcType 113 { bytes := artifactBytes, pos := 880, limit := 2571 } =
      .ok (Cache.raw.types.drop 82, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type82_decoded types_tail83_decoded

theorem types_tail81_decoded :
    Internal.vectorLoop funcType 114 { bytes := artifactBytes, pos := 871, limit := 2571 } =
      .ok (Cache.raw.types.drop 81, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type81_decoded types_tail82_decoded

theorem types_tail80_decoded :
    Internal.vectorLoop funcType 115 { bytes := artifactBytes, pos := 863, limit := 2571 } =
      .ok (Cache.raw.types.drop 80, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type80_decoded types_tail81_decoded

theorem types_tail79_decoded :
    Internal.vectorLoop funcType 116 { bytes := artifactBytes, pos := 855, limit := 2571 } =
      .ok (Cache.raw.types.drop 79, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type79_decoded types_tail80_decoded

theorem types_tail78_decoded :
    Internal.vectorLoop funcType 117 { bytes := artifactBytes, pos := 847, limit := 2571 } =
      .ok (Cache.raw.types.drop 78, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type78_decoded types_tail79_decoded

theorem types_tail77_decoded :
    Internal.vectorLoop funcType 118 { bytes := artifactBytes, pos := 838, limit := 2571 } =
      .ok (Cache.raw.types.drop 77, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type77_decoded types_tail78_decoded

theorem types_tail76_decoded :
    Internal.vectorLoop funcType 119 { bytes := artifactBytes, pos := 834, limit := 2571 } =
      .ok (Cache.raw.types.drop 76, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type76_decoded types_tail77_decoded

theorem types_tail75_decoded :
    Internal.vectorLoop funcType 120 { bytes := artifactBytes, pos := 816, limit := 2571 } =
      .ok (Cache.raw.types.drop 75, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type75_decoded types_tail76_decoded

theorem types_tail74_decoded :
    Internal.vectorLoop funcType 121 { bytes := artifactBytes, pos := 799, limit := 2571 } =
      .ok (Cache.raw.types.drop 74, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type74_decoded types_tail75_decoded

theorem types_tail73_decoded :
    Internal.vectorLoop funcType 122 { bytes := artifactBytes, pos := 765, limit := 2571 } =
      .ok (Cache.raw.types.drop 73, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type73_decoded types_tail74_decoded

theorem types_tail72_decoded :
    Internal.vectorLoop funcType 123 { bytes := artifactBytes, pos := 746, limit := 2571 } =
      .ok (Cache.raw.types.drop 72, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type72_decoded types_tail73_decoded

theorem types_tail71_decoded :
    Internal.vectorLoop funcType 124 { bytes := artifactBytes, pos := 739, limit := 2571 } =
      .ok (Cache.raw.types.drop 71, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type71_decoded types_tail72_decoded

theorem types_tail70_decoded :
    Internal.vectorLoop funcType 125 { bytes := artifactBytes, pos := 700, limit := 2571 } =
      .ok (Cache.raw.types.drop 70, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type70_decoded types_tail71_decoded

theorem types_tail69_decoded :
    Internal.vectorLoop funcType 126 { bytes := artifactBytes, pos := 688, limit := 2571 } =
      .ok (Cache.raw.types.drop 69, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type69_decoded types_tail70_decoded

theorem types_tail68_decoded :
    Internal.vectorLoop funcType 127 { bytes := artifactBytes, pos := 680, limit := 2571 } =
      .ok (Cache.raw.types.drop 68, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type68_decoded types_tail69_decoded


theorem types_tail67_decoded :
    Internal.vectorLoop funcType 128 { bytes := artifactBytes, pos := 665, limit := 2571 } =
      .ok (Cache.raw.types.drop 67, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type67_decoded types_tail68_decoded

theorem types_tail66_decoded :
    Internal.vectorLoop funcType 129 { bytes := artifactBytes, pos := 637, limit := 2571 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type66_decoded types_tail67_decoded

theorem types_tail65_decoded :
    Internal.vectorLoop funcType 130 { bytes := artifactBytes, pos := 627, limit := 2571 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type65_decoded types_tail66_decoded

theorem types_tail64_decoded :
    Internal.vectorLoop funcType 131 { bytes := artifactBytes, pos := 619, limit := 2571 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type64_decoded types_tail65_decoded

theorem types_tail63_decoded :
    Internal.vectorLoop funcType 132 { bytes := artifactBytes, pos := 612, limit := 2571 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type63_decoded types_tail64_decoded

theorem types_tail62_decoded :
    Internal.vectorLoop funcType 133 { bytes := artifactBytes, pos := 607, limit := 2571 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type62_decoded types_tail63_decoded

theorem types_tail61_decoded :
    Internal.vectorLoop funcType 134 { bytes := artifactBytes, pos := 601, limit := 2571 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type61_decoded types_tail62_decoded

theorem types_tail60_decoded :
    Internal.vectorLoop funcType 135 { bytes := artifactBytes, pos := 596, limit := 2571 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type60_decoded types_tail61_decoded

theorem types_tail59_decoded :
    Internal.vectorLoop funcType 136 { bytes := artifactBytes, pos := 591, limit := 2571 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type59_decoded types_tail60_decoded

theorem types_tail58_decoded :
    Internal.vectorLoop funcType 137 { bytes := artifactBytes, pos := 581, limit := 2571 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type58_decoded types_tail59_decoded

theorem types_tail57_decoded :
    Internal.vectorLoop funcType 138 { bytes := artifactBytes, pos := 575, limit := 2571 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type57_decoded types_tail58_decoded

theorem types_tail56_decoded :
    Internal.vectorLoop funcType 139 { bytes := artifactBytes, pos := 569, limit := 2571 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type56_decoded types_tail57_decoded

theorem types_tail55_decoded :
    Internal.vectorLoop funcType 140 { bytes := artifactBytes, pos := 563, limit := 2571 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type55_decoded types_tail56_decoded

theorem types_tail54_decoded :
    Internal.vectorLoop funcType 141 { bytes := artifactBytes, pos := 558, limit := 2571 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type54_decoded types_tail55_decoded

theorem types_tail53_decoded :
    Internal.vectorLoop funcType 142 { bytes := artifactBytes, pos := 552, limit := 2571 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type53_decoded types_tail54_decoded

theorem types_tail52_decoded :
    Internal.vectorLoop funcType 143 { bytes := artifactBytes, pos := 542, limit := 2571 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type52_decoded types_tail53_decoded


theorem types_tail51_decoded :
    Internal.vectorLoop funcType 144 { bytes := artifactBytes, pos := 531, limit := 2571 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type51_decoded types_tail52_decoded

theorem types_tail50_decoded :
    Internal.vectorLoop funcType 145 { bytes := artifactBytes, pos := 519, limit := 2571 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type50_decoded types_tail51_decoded

theorem types_tail49_decoded :
    Internal.vectorLoop funcType 146 { bytes := artifactBytes, pos := 507, limit := 2571 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50_decoded

theorem types_tail48_decoded :
    Internal.vectorLoop funcType 147 { bytes := artifactBytes, pos := 495, limit := 2571 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49_decoded

theorem types_tail47_decoded :
    Internal.vectorLoop funcType 148 { bytes := artifactBytes, pos := 480, limit := 2571 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48_decoded

theorem types_tail46_decoded :
    Internal.vectorLoop funcType 149 { bytes := artifactBytes, pos := 469, limit := 2571 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47_decoded

theorem types_tail45_decoded :
    Internal.vectorLoop funcType 150 { bytes := artifactBytes, pos := 461, limit := 2571 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46_decoded

theorem types_tail44_decoded :
    Internal.vectorLoop funcType 151 { bytes := artifactBytes, pos := 453, limit := 2571 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45_decoded

theorem types_tail43_decoded :
    Internal.vectorLoop funcType 152 { bytes := artifactBytes, pos := 445, limit := 2571 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44_decoded

theorem types_tail42_decoded :
    Internal.vectorLoop funcType 153 { bytes := artifactBytes, pos := 439, limit := 2571 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43_decoded

theorem types_tail41_decoded :
    Internal.vectorLoop funcType 154 { bytes := artifactBytes, pos := 433, limit := 2571 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42_decoded

theorem types_tail40_decoded :
    Internal.vectorLoop funcType 155 { bytes := artifactBytes, pos := 425, limit := 2571 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41_decoded

theorem types_tail39_decoded :
    Internal.vectorLoop funcType 156 { bytes := artifactBytes, pos := 419, limit := 2571 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40_decoded

theorem types_tail38_decoded :
    Internal.vectorLoop funcType 157 { bytes := artifactBytes, pos := 413, limit := 2571 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39_decoded

theorem types_tail37_decoded :
    Internal.vectorLoop funcType 158 { bytes := artifactBytes, pos := 407, limit := 2571 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38_decoded

theorem types_tail36_decoded :
    Internal.vectorLoop funcType 159 { bytes := artifactBytes, pos := 399, limit := 2571 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37_decoded


theorem types_tail35_decoded :
    Internal.vectorLoop funcType 160 { bytes := artifactBytes, pos := 394, limit := 2571 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36_decoded

theorem types_tail34_decoded :
    Internal.vectorLoop funcType 161 { bytes := artifactBytes, pos := 388, limit := 2571 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35_decoded

theorem types_tail33_decoded :
    Internal.vectorLoop funcType 162 { bytes := artifactBytes, pos := 383, limit := 2571 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34_decoded

theorem types_tail32_decoded :
    Internal.vectorLoop funcType 163 { bytes := artifactBytes, pos := 378, limit := 2571 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33_decoded

theorem types_tail31_decoded :
    Internal.vectorLoop funcType 164 { bytes := artifactBytes, pos := 373, limit := 2571 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32_decoded

theorem types_tail30_decoded :
    Internal.vectorLoop funcType 165 { bytes := artifactBytes, pos := 365, limit := 2571 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31_decoded

theorem types_tail29_decoded :
    Internal.vectorLoop funcType 166 { bytes := artifactBytes, pos := 360, limit := 2571 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30_decoded

theorem types_tail28_decoded :
    Internal.vectorLoop funcType 167 { bytes := artifactBytes, pos := 355, limit := 2571 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29_decoded

theorem types_tail27_decoded :
    Internal.vectorLoop funcType 168 { bytes := artifactBytes, pos := 350, limit := 2571 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28_decoded

theorem types_tail26_decoded :
    Internal.vectorLoop funcType 169 { bytes := artifactBytes, pos := 341, limit := 2571 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27_decoded

theorem types_tail25_decoded :
    Internal.vectorLoop funcType 170 { bytes := artifactBytes, pos := 333, limit := 2571 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26_decoded

theorem types_tail24_decoded :
    Internal.vectorLoop funcType 171 { bytes := artifactBytes, pos := 325, limit := 2571 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25_decoded

theorem types_tail23_decoded :
    Internal.vectorLoop funcType 172 { bytes := artifactBytes, pos := 317, limit := 2571 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24_decoded

theorem types_tail22_decoded :
    Internal.vectorLoop funcType 173 { bytes := artifactBytes, pos := 310, limit := 2571 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23_decoded

theorem types_tail21_decoded :
    Internal.vectorLoop funcType 174 { bytes := artifactBytes, pos := 303, limit := 2571 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22_decoded

theorem types_tail20_decoded :
    Internal.vectorLoop funcType 175 { bytes := artifactBytes, pos := 296, limit := 2571 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21_decoded


theorem types_tail19_decoded :
    Internal.vectorLoop funcType 176 { bytes := artifactBytes, pos := 289, limit := 2571 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20_decoded

theorem types_tail18_decoded :
    Internal.vectorLoop funcType 177 { bytes := artifactBytes, pos := 278, limit := 2571 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19_decoded

theorem types_tail17_decoded :
    Internal.vectorLoop funcType 178 { bytes := artifactBytes, pos := 268, limit := 2571 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18_decoded

theorem types_tail16_decoded :
    Internal.vectorLoop funcType 179 { bytes := artifactBytes, pos := 263, limit := 2571 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17_decoded

theorem types_tail15_decoded :
    Internal.vectorLoop funcType 180 { bytes := artifactBytes, pos := 241, limit := 2571 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16_decoded

theorem types_tail14_decoded :
    Internal.vectorLoop funcType 181 { bytes := artifactBytes, pos := 223, limit := 2571 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15_decoded

theorem types_tail13_decoded :
    Internal.vectorLoop funcType 182 { bytes := artifactBytes, pos := 205, limit := 2571 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14_decoded

theorem types_tail12_decoded :
    Internal.vectorLoop funcType 183 { bytes := artifactBytes, pos := 187, limit := 2571 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13_decoded

theorem types_tail11_decoded :
    Internal.vectorLoop funcType 184 { bytes := artifactBytes, pos := 180, limit := 2571 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12_decoded

theorem types_tail10_decoded :
    Internal.vectorLoop funcType 185 { bytes := artifactBytes, pos := 173, limit := 2571 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11_decoded

theorem types_tail9_decoded :
    Internal.vectorLoop funcType 186 { bytes := artifactBytes, pos := 155, limit := 2571 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10_decoded

theorem types_tail8_decoded :
    Internal.vectorLoop funcType 187 { bytes := artifactBytes, pos := 148, limit := 2571 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9_decoded

theorem types_tail7_decoded :
    Internal.vectorLoop funcType 188 { bytes := artifactBytes, pos := 117, limit := 2571 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8_decoded

theorem types_tail6_decoded :
    Internal.vectorLoop funcType 189 { bytes := artifactBytes, pos := 96, limit := 2571 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7_decoded

theorem types_tail5_decoded :
    Internal.vectorLoop funcType 190 { bytes := artifactBytes, pos := 76, limit := 2571 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6_decoded

theorem types_tail4_decoded :
    Internal.vectorLoop funcType 191 { bytes := artifactBytes, pos := 56, limit := 2571 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5_decoded


theorem types_tail3_decoded :
    Internal.vectorLoop funcType 192 { bytes := artifactBytes, pos := 46, limit := 2571 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4_decoded

theorem types_tail2_decoded :
    Internal.vectorLoop funcType 193 { bytes := artifactBytes, pos := 35, limit := 2571 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3_decoded

theorem types_tail1_decoded :
    Internal.vectorLoop funcType 194 { bytes := artifactBytes, pos := 21, limit := 2571 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2_decoded

theorem types_tail0_decoded :
    Internal.vectorLoop funcType 195 { bytes := artifactBytes, pos := 13, limit := 2571 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1_decoded

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 2571 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by
  refine vector_eq_of_parts (length := 195)
    (itemsStart := { bytes := artifactBytes, pos := 13, limit := 2571 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0_decoded

#print axioms types_vector_decoded

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 45644 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 2571, limit := 45644 }) := by
  refine sized_eq_of_parts (size := 2560)
    (payload := { bytes := artifactBytes, pos := 11, limit := 45644 }) (finish := { bytes := artifactBytes, pos := 2571, limit := 2571 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.EulerCertificate.Artifact
