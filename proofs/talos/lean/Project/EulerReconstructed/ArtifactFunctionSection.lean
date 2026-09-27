import Project.EulerReconstructed.ArtifactFunctionIndices0To31
import Project.EulerReconstructed.ArtifactFunctionIndices32To63
import Project.EulerReconstructed.ArtifactFunctionIndices64To95
import Project.EulerReconstructed.ArtifactFunctionIndices96To127
import Project.EulerReconstructed.ArtifactFunctionIndices128To152
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndices_tail153_decoded :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 1805, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 153, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by rfl

theorem functionIndices_tail152_decoded :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 1803, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 152, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex152_decoded functionIndices_tail153_decoded

theorem functionIndices_tail151_decoded :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 1801, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 151, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex151_decoded functionIndices_tail152_decoded

theorem functionIndices_tail150_decoded :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 1799, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 150, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex150_decoded functionIndices_tail151_decoded

theorem functionIndices_tail149_decoded :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 1797, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 149, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex149_decoded functionIndices_tail150_decoded

theorem functionIndices_tail148_decoded :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 1795, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 148, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex148_decoded functionIndices_tail149_decoded

theorem functionIndices_tail147_decoded :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 1793, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 147, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex147_decoded functionIndices_tail148_decoded

theorem functionIndices_tail146_decoded :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 1791, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 146, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex146_decoded functionIndices_tail147_decoded

theorem functionIndices_tail145_decoded :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 1789, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 145, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex145_decoded functionIndices_tail146_decoded

theorem functionIndices_tail144_decoded :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 1787, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 144, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex144_decoded functionIndices_tail145_decoded

theorem functionIndices_tail143_decoded :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 1785, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 143, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex143_decoded functionIndices_tail144_decoded

theorem functionIndices_tail142_decoded :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 1783, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 142, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex142_decoded functionIndices_tail143_decoded

theorem functionIndices_tail141_decoded :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 1781, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 141, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex141_decoded functionIndices_tail142_decoded

theorem functionIndices_tail140_decoded :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 1779, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 140, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex140_decoded functionIndices_tail141_decoded

theorem functionIndices_tail139_decoded :
    Internal.vectorLoop Leb.u32 14 { bytes := artifactBytes, pos := 1777, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 139, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex139_decoded functionIndices_tail140_decoded

theorem functionIndices_tail138_decoded :
    Internal.vectorLoop Leb.u32 15 { bytes := artifactBytes, pos := 1775, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 138, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex138_decoded functionIndices_tail139_decoded

theorem functionIndices_tail137_decoded :
    Internal.vectorLoop Leb.u32 16 { bytes := artifactBytes, pos := 1773, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 137, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex137_decoded functionIndices_tail138_decoded

theorem functionIndices_tail136_decoded :
    Internal.vectorLoop Leb.u32 17 { bytes := artifactBytes, pos := 1771, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 136, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex136_decoded functionIndices_tail137_decoded

theorem functionIndices_tail135_decoded :
    Internal.vectorLoop Leb.u32 18 { bytes := artifactBytes, pos := 1769, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 135, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex135_decoded functionIndices_tail136_decoded

theorem functionIndices_tail134_decoded :
    Internal.vectorLoop Leb.u32 19 { bytes := artifactBytes, pos := 1767, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 134, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex134_decoded functionIndices_tail135_decoded

theorem functionIndices_tail133_decoded :
    Internal.vectorLoop Leb.u32 20 { bytes := artifactBytes, pos := 1765, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 133, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex133_decoded functionIndices_tail134_decoded

theorem functionIndices_tail132_decoded :
    Internal.vectorLoop Leb.u32 21 { bytes := artifactBytes, pos := 1763, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 132, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex132_decoded functionIndices_tail133_decoded

theorem functionIndices_tail131_decoded :
    Internal.vectorLoop Leb.u32 22 { bytes := artifactBytes, pos := 1761, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 131, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex131_decoded functionIndices_tail132_decoded

theorem functionIndices_tail130_decoded :
    Internal.vectorLoop Leb.u32 23 { bytes := artifactBytes, pos := 1759, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 130, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex130_decoded functionIndices_tail131_decoded

theorem functionIndices_tail129_decoded :
    Internal.vectorLoop Leb.u32 24 { bytes := artifactBytes, pos := 1757, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 129, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex129_decoded functionIndices_tail130_decoded

theorem functionIndices_tail128_decoded :
    Internal.vectorLoop Leb.u32 25 { bytes := artifactBytes, pos := 1755, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 128, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex128_decoded functionIndices_tail129_decoded

theorem functionIndices_tail127_decoded :
    Internal.vectorLoop Leb.u32 26 { bytes := artifactBytes, pos := 1754, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 127, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex127_decoded functionIndices_tail128_decoded

theorem functionIndices_tail126_decoded :
    Internal.vectorLoop Leb.u32 27 { bytes := artifactBytes, pos := 1753, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 126, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex126_decoded functionIndices_tail127_decoded

theorem functionIndices_tail125_decoded :
    Internal.vectorLoop Leb.u32 28 { bytes := artifactBytes, pos := 1752, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 125, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex125_decoded functionIndices_tail126_decoded

theorem functionIndices_tail124_decoded :
    Internal.vectorLoop Leb.u32 29 { bytes := artifactBytes, pos := 1751, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 124, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex124_decoded functionIndices_tail125_decoded

theorem functionIndices_tail123_decoded :
    Internal.vectorLoop Leb.u32 30 { bytes := artifactBytes, pos := 1750, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 123, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex123_decoded functionIndices_tail124_decoded

theorem functionIndices_tail122_decoded :
    Internal.vectorLoop Leb.u32 31 { bytes := artifactBytes, pos := 1749, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 122, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex122_decoded functionIndices_tail123_decoded

theorem functionIndices_tail121_decoded :
    Internal.vectorLoop Leb.u32 32 { bytes := artifactBytes, pos := 1748, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 121, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex121_decoded functionIndices_tail122_decoded

theorem functionIndices_tail120_decoded :
    Internal.vectorLoop Leb.u32 33 { bytes := artifactBytes, pos := 1747, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 120, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex120_decoded functionIndices_tail121_decoded

theorem functionIndices_tail119_decoded :
    Internal.vectorLoop Leb.u32 34 { bytes := artifactBytes, pos := 1746, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 119, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex119_decoded functionIndices_tail120_decoded

theorem functionIndices_tail118_decoded :
    Internal.vectorLoop Leb.u32 35 { bytes := artifactBytes, pos := 1745, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 118, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex118_decoded functionIndices_tail119_decoded

theorem functionIndices_tail117_decoded :
    Internal.vectorLoop Leb.u32 36 { bytes := artifactBytes, pos := 1744, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 117, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex117_decoded functionIndices_tail118_decoded

theorem functionIndices_tail116_decoded :
    Internal.vectorLoop Leb.u32 37 { bytes := artifactBytes, pos := 1743, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 116, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex116_decoded functionIndices_tail117_decoded

theorem functionIndices_tail115_decoded :
    Internal.vectorLoop Leb.u32 38 { bytes := artifactBytes, pos := 1742, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 115, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex115_decoded functionIndices_tail116_decoded

theorem functionIndices_tail114_decoded :
    Internal.vectorLoop Leb.u32 39 { bytes := artifactBytes, pos := 1741, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 114, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex114_decoded functionIndices_tail115_decoded

theorem functionIndices_tail113_decoded :
    Internal.vectorLoop Leb.u32 40 { bytes := artifactBytes, pos := 1740, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 113, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex113_decoded functionIndices_tail114_decoded

theorem functionIndices_tail112_decoded :
    Internal.vectorLoop Leb.u32 41 { bytes := artifactBytes, pos := 1739, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 112, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex112_decoded functionIndices_tail113_decoded

theorem functionIndices_tail111_decoded :
    Internal.vectorLoop Leb.u32 42 { bytes := artifactBytes, pos := 1738, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 111, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex111_decoded functionIndices_tail112_decoded

theorem functionIndices_tail110_decoded :
    Internal.vectorLoop Leb.u32 43 { bytes := artifactBytes, pos := 1737, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 110, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex110_decoded functionIndices_tail111_decoded

theorem functionIndices_tail109_decoded :
    Internal.vectorLoop Leb.u32 44 { bytes := artifactBytes, pos := 1736, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 109, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex109_decoded functionIndices_tail110_decoded

theorem functionIndices_tail108_decoded :
    Internal.vectorLoop Leb.u32 45 { bytes := artifactBytes, pos := 1735, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 108, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex108_decoded functionIndices_tail109_decoded

theorem functionIndices_tail107_decoded :
    Internal.vectorLoop Leb.u32 46 { bytes := artifactBytes, pos := 1734, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 107, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex107_decoded functionIndices_tail108_decoded

theorem functionIndices_tail106_decoded :
    Internal.vectorLoop Leb.u32 47 { bytes := artifactBytes, pos := 1733, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 106, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex106_decoded functionIndices_tail107_decoded

theorem functionIndices_tail105_decoded :
    Internal.vectorLoop Leb.u32 48 { bytes := artifactBytes, pos := 1732, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 105, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex105_decoded functionIndices_tail106_decoded

theorem functionIndices_tail104_decoded :
    Internal.vectorLoop Leb.u32 49 { bytes := artifactBytes, pos := 1731, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 104, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex104_decoded functionIndices_tail105_decoded

theorem functionIndices_tail103_decoded :
    Internal.vectorLoop Leb.u32 50 { bytes := artifactBytes, pos := 1730, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 103, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex103_decoded functionIndices_tail104_decoded

theorem functionIndices_tail102_decoded :
    Internal.vectorLoop Leb.u32 51 { bytes := artifactBytes, pos := 1729, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 102, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex102_decoded functionIndices_tail103_decoded

theorem functionIndices_tail101_decoded :
    Internal.vectorLoop Leb.u32 52 { bytes := artifactBytes, pos := 1728, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 101, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex101_decoded functionIndices_tail102_decoded

theorem functionIndices_tail100_decoded :
    Internal.vectorLoop Leb.u32 53 { bytes := artifactBytes, pos := 1727, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 100, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex100_decoded functionIndices_tail101_decoded

theorem functionIndices_tail99_decoded :
    Internal.vectorLoop Leb.u32 54 { bytes := artifactBytes, pos := 1726, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 99, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex99_decoded functionIndices_tail100_decoded

theorem functionIndices_tail98_decoded :
    Internal.vectorLoop Leb.u32 55 { bytes := artifactBytes, pos := 1725, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 98, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex98_decoded functionIndices_tail99_decoded

theorem functionIndices_tail97_decoded :
    Internal.vectorLoop Leb.u32 56 { bytes := artifactBytes, pos := 1724, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 97, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex97_decoded functionIndices_tail98_decoded

theorem functionIndices_tail96_decoded :
    Internal.vectorLoop Leb.u32 57 { bytes := artifactBytes, pos := 1723, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 96, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex96_decoded functionIndices_tail97_decoded

theorem functionIndices_tail95_decoded :
    Internal.vectorLoop Leb.u32 58 { bytes := artifactBytes, pos := 1722, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 95, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex95_decoded functionIndices_tail96_decoded

theorem functionIndices_tail94_decoded :
    Internal.vectorLoop Leb.u32 59 { bytes := artifactBytes, pos := 1721, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 94, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex94_decoded functionIndices_tail95_decoded

theorem functionIndices_tail93_decoded :
    Internal.vectorLoop Leb.u32 60 { bytes := artifactBytes, pos := 1720, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 93, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex93_decoded functionIndices_tail94_decoded

theorem functionIndices_tail92_decoded :
    Internal.vectorLoop Leb.u32 61 { bytes := artifactBytes, pos := 1719, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 92, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex92_decoded functionIndices_tail93_decoded

theorem functionIndices_tail91_decoded :
    Internal.vectorLoop Leb.u32 62 { bytes := artifactBytes, pos := 1718, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 91, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex91_decoded functionIndices_tail92_decoded

theorem functionIndices_tail90_decoded :
    Internal.vectorLoop Leb.u32 63 { bytes := artifactBytes, pos := 1717, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 90, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex90_decoded functionIndices_tail91_decoded

theorem functionIndices_tail89_decoded :
    Internal.vectorLoop Leb.u32 64 { bytes := artifactBytes, pos := 1716, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 89, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex89_decoded functionIndices_tail90_decoded

theorem functionIndices_tail88_decoded :
    Internal.vectorLoop Leb.u32 65 { bytes := artifactBytes, pos := 1715, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 88, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex88_decoded functionIndices_tail89_decoded

theorem functionIndices_tail87_decoded :
    Internal.vectorLoop Leb.u32 66 { bytes := artifactBytes, pos := 1714, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 87, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex87_decoded functionIndices_tail88_decoded

theorem functionIndices_tail86_decoded :
    Internal.vectorLoop Leb.u32 67 { bytes := artifactBytes, pos := 1713, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 86, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex86_decoded functionIndices_tail87_decoded

theorem functionIndices_tail85_decoded :
    Internal.vectorLoop Leb.u32 68 { bytes := artifactBytes, pos := 1712, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 85, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex85_decoded functionIndices_tail86_decoded

theorem functionIndices_tail84_decoded :
    Internal.vectorLoop Leb.u32 69 { bytes := artifactBytes, pos := 1711, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 84, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex84_decoded functionIndices_tail85_decoded

theorem functionIndices_tail83_decoded :
    Internal.vectorLoop Leb.u32 70 { bytes := artifactBytes, pos := 1710, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 83, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex83_decoded functionIndices_tail84_decoded

theorem functionIndices_tail82_decoded :
    Internal.vectorLoop Leb.u32 71 { bytes := artifactBytes, pos := 1709, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 82, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex82_decoded functionIndices_tail83_decoded

theorem functionIndices_tail81_decoded :
    Internal.vectorLoop Leb.u32 72 { bytes := artifactBytes, pos := 1708, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 81, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex81_decoded functionIndices_tail82_decoded

theorem functionIndices_tail80_decoded :
    Internal.vectorLoop Leb.u32 73 { bytes := artifactBytes, pos := 1707, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 80, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex80_decoded functionIndices_tail81_decoded

theorem functionIndices_tail79_decoded :
    Internal.vectorLoop Leb.u32 74 { bytes := artifactBytes, pos := 1706, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 79, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex79_decoded functionIndices_tail80_decoded

theorem functionIndices_tail78_decoded :
    Internal.vectorLoop Leb.u32 75 { bytes := artifactBytes, pos := 1705, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 78, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex78_decoded functionIndices_tail79_decoded

theorem functionIndices_tail77_decoded :
    Internal.vectorLoop Leb.u32 76 { bytes := artifactBytes, pos := 1704, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 77, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex77_decoded functionIndices_tail78_decoded

theorem functionIndices_tail76_decoded :
    Internal.vectorLoop Leb.u32 77 { bytes := artifactBytes, pos := 1703, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 76, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex76_decoded functionIndices_tail77_decoded

theorem functionIndices_tail75_decoded :
    Internal.vectorLoop Leb.u32 78 { bytes := artifactBytes, pos := 1702, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 75, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex75_decoded functionIndices_tail76_decoded

theorem functionIndices_tail74_decoded :
    Internal.vectorLoop Leb.u32 79 { bytes := artifactBytes, pos := 1701, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 74, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex74_decoded functionIndices_tail75_decoded

theorem functionIndices_tail73_decoded :
    Internal.vectorLoop Leb.u32 80 { bytes := artifactBytes, pos := 1700, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 73, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex73_decoded functionIndices_tail74_decoded

theorem functionIndices_tail72_decoded :
    Internal.vectorLoop Leb.u32 81 { bytes := artifactBytes, pos := 1699, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 72, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex72_decoded functionIndices_tail73_decoded

theorem functionIndices_tail71_decoded :
    Internal.vectorLoop Leb.u32 82 { bytes := artifactBytes, pos := 1698, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 71, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex71_decoded functionIndices_tail72_decoded

theorem functionIndices_tail70_decoded :
    Internal.vectorLoop Leb.u32 83 { bytes := artifactBytes, pos := 1697, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 70, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex70_decoded functionIndices_tail71_decoded

theorem functionIndices_tail69_decoded :
    Internal.vectorLoop Leb.u32 84 { bytes := artifactBytes, pos := 1696, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 69, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex69_decoded functionIndices_tail70_decoded

theorem functionIndices_tail68_decoded :
    Internal.vectorLoop Leb.u32 85 { bytes := artifactBytes, pos := 1695, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 68, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex68_decoded functionIndices_tail69_decoded

theorem functionIndices_tail67_decoded :
    Internal.vectorLoop Leb.u32 86 { bytes := artifactBytes, pos := 1694, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 67, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex67_decoded functionIndices_tail68_decoded

theorem functionIndices_tail66_decoded :
    Internal.vectorLoop Leb.u32 87 { bytes := artifactBytes, pos := 1693, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 66, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex66_decoded functionIndices_tail67_decoded

theorem functionIndices_tail65_decoded :
    Internal.vectorLoop Leb.u32 88 { bytes := artifactBytes, pos := 1692, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 65, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex65_decoded functionIndices_tail66_decoded

theorem functionIndices_tail64_decoded :
    Internal.vectorLoop Leb.u32 89 { bytes := artifactBytes, pos := 1691, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 64, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex64_decoded functionIndices_tail65_decoded

theorem functionIndices_tail63_decoded :
    Internal.vectorLoop Leb.u32 90 { bytes := artifactBytes, pos := 1690, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 63, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex63_decoded functionIndices_tail64_decoded

theorem functionIndices_tail62_decoded :
    Internal.vectorLoop Leb.u32 91 { bytes := artifactBytes, pos := 1689, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 62, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex62_decoded functionIndices_tail63_decoded

theorem functionIndices_tail61_decoded :
    Internal.vectorLoop Leb.u32 92 { bytes := artifactBytes, pos := 1688, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 61, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex61_decoded functionIndices_tail62_decoded

theorem functionIndices_tail60_decoded :
    Internal.vectorLoop Leb.u32 93 { bytes := artifactBytes, pos := 1687, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 60, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex60_decoded functionIndices_tail61_decoded

theorem functionIndices_tail59_decoded :
    Internal.vectorLoop Leb.u32 94 { bytes := artifactBytes, pos := 1686, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 59, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex59_decoded functionIndices_tail60_decoded

theorem functionIndices_tail58_decoded :
    Internal.vectorLoop Leb.u32 95 { bytes := artifactBytes, pos := 1685, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 58, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex58_decoded functionIndices_tail59_decoded

theorem functionIndices_tail57_decoded :
    Internal.vectorLoop Leb.u32 96 { bytes := artifactBytes, pos := 1684, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 57, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex57_decoded functionIndices_tail58_decoded

theorem functionIndices_tail56_decoded :
    Internal.vectorLoop Leb.u32 97 { bytes := artifactBytes, pos := 1683, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 56, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex56_decoded functionIndices_tail57_decoded

theorem functionIndices_tail55_decoded :
    Internal.vectorLoop Leb.u32 98 { bytes := artifactBytes, pos := 1682, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 55, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex55_decoded functionIndices_tail56_decoded

theorem functionIndices_tail54_decoded :
    Internal.vectorLoop Leb.u32 99 { bytes := artifactBytes, pos := 1681, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 54, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex54_decoded functionIndices_tail55_decoded

theorem functionIndices_tail53_decoded :
    Internal.vectorLoop Leb.u32 100 { bytes := artifactBytes, pos := 1680, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 53, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex53_decoded functionIndices_tail54_decoded

theorem functionIndices_tail52_decoded :
    Internal.vectorLoop Leb.u32 101 { bytes := artifactBytes, pos := 1679, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 52, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex52_decoded functionIndices_tail53_decoded

theorem functionIndices_tail51_decoded :
    Internal.vectorLoop Leb.u32 102 { bytes := artifactBytes, pos := 1678, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 51, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex51_decoded functionIndices_tail52_decoded

theorem functionIndices_tail50_decoded :
    Internal.vectorLoop Leb.u32 103 { bytes := artifactBytes, pos := 1677, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 50, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex50_decoded functionIndices_tail51_decoded

theorem functionIndices_tail49_decoded :
    Internal.vectorLoop Leb.u32 104 { bytes := artifactBytes, pos := 1676, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 49, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex49_decoded functionIndices_tail50_decoded

theorem functionIndices_tail48_decoded :
    Internal.vectorLoop Leb.u32 105 { bytes := artifactBytes, pos := 1675, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 48, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex48_decoded functionIndices_tail49_decoded

theorem functionIndices_tail47_decoded :
    Internal.vectorLoop Leb.u32 106 { bytes := artifactBytes, pos := 1674, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 47, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex47_decoded functionIndices_tail48_decoded

theorem functionIndices_tail46_decoded :
    Internal.vectorLoop Leb.u32 107 { bytes := artifactBytes, pos := 1673, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 46, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex46_decoded functionIndices_tail47_decoded

theorem functionIndices_tail45_decoded :
    Internal.vectorLoop Leb.u32 108 { bytes := artifactBytes, pos := 1672, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 45, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex45_decoded functionIndices_tail46_decoded

theorem functionIndices_tail44_decoded :
    Internal.vectorLoop Leb.u32 109 { bytes := artifactBytes, pos := 1671, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 44, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex44_decoded functionIndices_tail45_decoded

theorem functionIndices_tail43_decoded :
    Internal.vectorLoop Leb.u32 110 { bytes := artifactBytes, pos := 1670, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex43_decoded functionIndices_tail44_decoded

theorem functionIndices_tail42_decoded :
    Internal.vectorLoop Leb.u32 111 { bytes := artifactBytes, pos := 1669, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex42_decoded functionIndices_tail43_decoded

theorem functionIndices_tail41_decoded :
    Internal.vectorLoop Leb.u32 112 { bytes := artifactBytes, pos := 1668, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex41_decoded functionIndices_tail42_decoded

theorem functionIndices_tail40_decoded :
    Internal.vectorLoop Leb.u32 113 { bytes := artifactBytes, pos := 1667, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex40_decoded functionIndices_tail41_decoded

theorem functionIndices_tail39_decoded :
    Internal.vectorLoop Leb.u32 114 { bytes := artifactBytes, pos := 1666, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex39_decoded functionIndices_tail40_decoded

theorem functionIndices_tail38_decoded :
    Internal.vectorLoop Leb.u32 115 { bytes := artifactBytes, pos := 1665, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex38_decoded functionIndices_tail39_decoded

theorem functionIndices_tail37_decoded :
    Internal.vectorLoop Leb.u32 116 { bytes := artifactBytes, pos := 1664, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex37_decoded functionIndices_tail38_decoded

theorem functionIndices_tail36_decoded :
    Internal.vectorLoop Leb.u32 117 { bytes := artifactBytes, pos := 1663, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex36_decoded functionIndices_tail37_decoded

theorem functionIndices_tail35_decoded :
    Internal.vectorLoop Leb.u32 118 { bytes := artifactBytes, pos := 1662, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex35_decoded functionIndices_tail36_decoded

theorem functionIndices_tail34_decoded :
    Internal.vectorLoop Leb.u32 119 { bytes := artifactBytes, pos := 1661, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex34_decoded functionIndices_tail35_decoded

theorem functionIndices_tail33_decoded :
    Internal.vectorLoop Leb.u32 120 { bytes := artifactBytes, pos := 1660, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex33_decoded functionIndices_tail34_decoded

theorem functionIndices_tail32_decoded :
    Internal.vectorLoop Leb.u32 121 { bytes := artifactBytes, pos := 1659, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex32_decoded functionIndices_tail33_decoded

theorem functionIndices_tail31_decoded :
    Internal.vectorLoop Leb.u32 122 { bytes := artifactBytes, pos := 1658, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex31_decoded functionIndices_tail32_decoded

theorem functionIndices_tail30_decoded :
    Internal.vectorLoop Leb.u32 123 { bytes := artifactBytes, pos := 1657, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex30_decoded functionIndices_tail31_decoded

theorem functionIndices_tail29_decoded :
    Internal.vectorLoop Leb.u32 124 { bytes := artifactBytes, pos := 1656, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex29_decoded functionIndices_tail30_decoded

theorem functionIndices_tail28_decoded :
    Internal.vectorLoop Leb.u32 125 { bytes := artifactBytes, pos := 1655, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex28_decoded functionIndices_tail29_decoded

theorem functionIndices_tail27_decoded :
    Internal.vectorLoop Leb.u32 126 { bytes := artifactBytes, pos := 1654, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex27_decoded functionIndices_tail28_decoded

theorem functionIndices_tail26_decoded :
    Internal.vectorLoop Leb.u32 127 { bytes := artifactBytes, pos := 1653, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex26_decoded functionIndices_tail27_decoded

theorem functionIndices_tail25_decoded :
    Internal.vectorLoop Leb.u32 128 { bytes := artifactBytes, pos := 1652, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex25_decoded functionIndices_tail26_decoded

theorem functionIndices_tail24_decoded :
    Internal.vectorLoop Leb.u32 129 { bytes := artifactBytes, pos := 1651, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex24_decoded functionIndices_tail25_decoded

theorem functionIndices_tail23_decoded :
    Internal.vectorLoop Leb.u32 130 { bytes := artifactBytes, pos := 1650, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex23_decoded functionIndices_tail24_decoded

theorem functionIndices_tail22_decoded :
    Internal.vectorLoop Leb.u32 131 { bytes := artifactBytes, pos := 1649, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex22_decoded functionIndices_tail23_decoded

theorem functionIndices_tail21_decoded :
    Internal.vectorLoop Leb.u32 132 { bytes := artifactBytes, pos := 1648, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex21_decoded functionIndices_tail22_decoded

theorem functionIndices_tail20_decoded :
    Internal.vectorLoop Leb.u32 133 { bytes := artifactBytes, pos := 1647, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex20_decoded functionIndices_tail21_decoded

theorem functionIndices_tail19_decoded :
    Internal.vectorLoop Leb.u32 134 { bytes := artifactBytes, pos := 1646, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex19_decoded functionIndices_tail20_decoded

theorem functionIndices_tail18_decoded :
    Internal.vectorLoop Leb.u32 135 { bytes := artifactBytes, pos := 1645, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex18_decoded functionIndices_tail19_decoded

theorem functionIndices_tail17_decoded :
    Internal.vectorLoop Leb.u32 136 { bytes := artifactBytes, pos := 1644, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex17_decoded functionIndices_tail18_decoded

theorem functionIndices_tail16_decoded :
    Internal.vectorLoop Leb.u32 137 { bytes := artifactBytes, pos := 1643, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex16_decoded functionIndices_tail17_decoded

theorem functionIndices_tail15_decoded :
    Internal.vectorLoop Leb.u32 138 { bytes := artifactBytes, pos := 1642, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex15_decoded functionIndices_tail16_decoded

theorem functionIndices_tail14_decoded :
    Internal.vectorLoop Leb.u32 139 { bytes := artifactBytes, pos := 1641, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex14_decoded functionIndices_tail15_decoded

theorem functionIndices_tail13_decoded :
    Internal.vectorLoop Leb.u32 140 { bytes := artifactBytes, pos := 1640, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex13_decoded functionIndices_tail14_decoded

theorem functionIndices_tail12_decoded :
    Internal.vectorLoop Leb.u32 141 { bytes := artifactBytes, pos := 1639, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex12_decoded functionIndices_tail13_decoded

theorem functionIndices_tail11_decoded :
    Internal.vectorLoop Leb.u32 142 { bytes := artifactBytes, pos := 1638, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex11_decoded functionIndices_tail12_decoded

theorem functionIndices_tail10_decoded :
    Internal.vectorLoop Leb.u32 143 { bytes := artifactBytes, pos := 1637, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex10_decoded functionIndices_tail11_decoded

theorem functionIndices_tail9_decoded :
    Internal.vectorLoop Leb.u32 144 { bytes := artifactBytes, pos := 1636, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex9_decoded functionIndices_tail10_decoded

theorem functionIndices_tail8_decoded :
    Internal.vectorLoop Leb.u32 145 { bytes := artifactBytes, pos := 1635, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex8_decoded functionIndices_tail9_decoded

theorem functionIndices_tail7_decoded :
    Internal.vectorLoop Leb.u32 146 { bytes := artifactBytes, pos := 1634, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex7_decoded functionIndices_tail8_decoded

theorem functionIndices_tail6_decoded :
    Internal.vectorLoop Leb.u32 147 { bytes := artifactBytes, pos := 1633, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex6_decoded functionIndices_tail7_decoded

theorem functionIndices_tail5_decoded :
    Internal.vectorLoop Leb.u32 148 { bytes := artifactBytes, pos := 1632, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex5_decoded functionIndices_tail6_decoded

theorem functionIndices_tail4_decoded :
    Internal.vectorLoop Leb.u32 149 { bytes := artifactBytes, pos := 1631, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex4_decoded functionIndices_tail5_decoded

theorem functionIndices_tail3_decoded :
    Internal.vectorLoop Leb.u32 150 { bytes := artifactBytes, pos := 1630, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex3_decoded functionIndices_tail4_decoded

theorem functionIndices_tail2_decoded :
    Internal.vectorLoop Leb.u32 151 { bytes := artifactBytes, pos := 1629, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex2_decoded functionIndices_tail3_decoded

theorem functionIndices_tail1_decoded :
    Internal.vectorLoop Leb.u32 152 { bytes := artifactBytes, pos := 1628, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex1_decoded functionIndices_tail2_decoded

theorem functionIndices_tail0_decoded :
    Internal.vectorLoop Leb.u32 153 { bytes := artifactBytes, pos := 1627, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  exact vectorLoop_eq_cons functionIndex0_decoded functionIndices_tail1_decoded

theorem functionIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 1625, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by
  refine vector_eq_of_parts (length := 153) (itemsStart := { bytes := artifactBytes, pos := 1627, limit := 1805 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionIndices_tail0_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 1623, limit := 30726 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 1805, limit := 30726 }) := by
  refine sized_eq_of_parts (size := 180)
    (payload := { bytes := artifactBytes, pos := 1625, limit := 30726 })
    (finish := { bytes := artifactBytes, pos := 1805, limit := 1805 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.EulerReconstructed.Artifact
