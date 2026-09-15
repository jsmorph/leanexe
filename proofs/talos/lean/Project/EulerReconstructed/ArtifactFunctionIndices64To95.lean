import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex64_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1691, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[64]!, { bytes := artifactBytes, pos := 1692, limit := 1805 }) := by cbv

theorem functionIndex65_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1692, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[65]!, { bytes := artifactBytes, pos := 1693, limit := 1805 }) := by cbv

theorem functionIndex66_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1693, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[66]!, { bytes := artifactBytes, pos := 1694, limit := 1805 }) := by cbv

theorem functionIndex67_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1694, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[67]!, { bytes := artifactBytes, pos := 1695, limit := 1805 }) := by cbv

theorem functionIndex68_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1695, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[68]!, { bytes := artifactBytes, pos := 1696, limit := 1805 }) := by cbv

theorem functionIndex69_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1696, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[69]!, { bytes := artifactBytes, pos := 1697, limit := 1805 }) := by cbv

theorem functionIndex70_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1697, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[70]!, { bytes := artifactBytes, pos := 1698, limit := 1805 }) := by cbv

theorem functionIndex71_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1698, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[71]!, { bytes := artifactBytes, pos := 1699, limit := 1805 }) := by cbv

theorem functionIndex72_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1699, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[72]!, { bytes := artifactBytes, pos := 1700, limit := 1805 }) := by cbv

theorem functionIndex73_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1700, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[73]!, { bytes := artifactBytes, pos := 1701, limit := 1805 }) := by cbv

theorem functionIndex74_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1701, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[74]!, { bytes := artifactBytes, pos := 1702, limit := 1805 }) := by cbv

theorem functionIndex75_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1702, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[75]!, { bytes := artifactBytes, pos := 1703, limit := 1805 }) := by cbv

theorem functionIndex76_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1703, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[76]!, { bytes := artifactBytes, pos := 1704, limit := 1805 }) := by cbv

theorem functionIndex77_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1704, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[77]!, { bytes := artifactBytes, pos := 1705, limit := 1805 }) := by cbv

theorem functionIndex78_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1705, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[78]!, { bytes := artifactBytes, pos := 1706, limit := 1805 }) := by cbv

theorem functionIndex79_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1706, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[79]!, { bytes := artifactBytes, pos := 1707, limit := 1805 }) := by cbv

theorem functionIndex80_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1707, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[80]!, { bytes := artifactBytes, pos := 1708, limit := 1805 }) := by cbv

theorem functionIndex81_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1708, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[81]!, { bytes := artifactBytes, pos := 1709, limit := 1805 }) := by cbv

theorem functionIndex82_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1709, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[82]!, { bytes := artifactBytes, pos := 1710, limit := 1805 }) := by cbv

theorem functionIndex83_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1710, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[83]!, { bytes := artifactBytes, pos := 1711, limit := 1805 }) := by cbv

theorem functionIndex84_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1711, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[84]!, { bytes := artifactBytes, pos := 1712, limit := 1805 }) := by cbv

theorem functionIndex85_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1712, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[85]!, { bytes := artifactBytes, pos := 1713, limit := 1805 }) := by cbv

theorem functionIndex86_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1713, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[86]!, { bytes := artifactBytes, pos := 1714, limit := 1805 }) := by cbv

theorem functionIndex87_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1714, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[87]!, { bytes := artifactBytes, pos := 1715, limit := 1805 }) := by cbv

theorem functionIndex88_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1715, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[88]!, { bytes := artifactBytes, pos := 1716, limit := 1805 }) := by cbv

theorem functionIndex89_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1716, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[89]!, { bytes := artifactBytes, pos := 1717, limit := 1805 }) := by cbv

theorem functionIndex90_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1717, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[90]!, { bytes := artifactBytes, pos := 1718, limit := 1805 }) := by cbv

theorem functionIndex91_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1718, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[91]!, { bytes := artifactBytes, pos := 1719, limit := 1805 }) := by cbv

theorem functionIndex92_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1719, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[92]!, { bytes := artifactBytes, pos := 1720, limit := 1805 }) := by cbv

theorem functionIndex93_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1720, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[93]!, { bytes := artifactBytes, pos := 1721, limit := 1805 }) := by cbv

theorem functionIndex94_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1721, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[94]!, { bytes := artifactBytes, pos := 1722, limit := 1805 }) := by cbv

theorem functionIndex95_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1722, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[95]!, { bytes := artifactBytes, pos := 1723, limit := 1805 }) := by cbv

#print axioms functionIndex95_decoded

end Project.EulerReconstructed.Artifact
