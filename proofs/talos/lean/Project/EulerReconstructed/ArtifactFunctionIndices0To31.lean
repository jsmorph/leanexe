import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1627, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 1628, limit := 1805 }) := by cbv

theorem functionIndex1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1628, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 1629, limit := 1805 }) := by cbv

theorem functionIndex2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1629, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 1630, limit := 1805 }) := by cbv

theorem functionIndex3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1630, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 1631, limit := 1805 }) := by cbv

theorem functionIndex4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1631, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 1632, limit := 1805 }) := by cbv

theorem functionIndex5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1632, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 1633, limit := 1805 }) := by cbv

theorem functionIndex6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1633, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 1634, limit := 1805 }) := by cbv

theorem functionIndex7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1634, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 1635, limit := 1805 }) := by cbv

theorem functionIndex8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1635, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 1636, limit := 1805 }) := by cbv

theorem functionIndex9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1636, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 1637, limit := 1805 }) := by cbv

theorem functionIndex10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1637, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 1638, limit := 1805 }) := by cbv

theorem functionIndex11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1638, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 1639, limit := 1805 }) := by cbv

theorem functionIndex12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1639, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 1640, limit := 1805 }) := by cbv

theorem functionIndex13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1640, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 1641, limit := 1805 }) := by cbv

theorem functionIndex14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1641, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 1642, limit := 1805 }) := by cbv

theorem functionIndex15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1642, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 1643, limit := 1805 }) := by cbv

theorem functionIndex16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1643, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 1644, limit := 1805 }) := by cbv

theorem functionIndex17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1644, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 1645, limit := 1805 }) := by cbv

theorem functionIndex18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1645, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 1646, limit := 1805 }) := by cbv

theorem functionIndex19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1646, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 1647, limit := 1805 }) := by cbv

theorem functionIndex20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1647, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 1648, limit := 1805 }) := by cbv

theorem functionIndex21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1648, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 1649, limit := 1805 }) := by cbv

theorem functionIndex22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1649, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 1650, limit := 1805 }) := by cbv

theorem functionIndex23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1650, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 1651, limit := 1805 }) := by cbv

theorem functionIndex24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1651, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 1652, limit := 1805 }) := by cbv

theorem functionIndex25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1652, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 1653, limit := 1805 }) := by cbv

theorem functionIndex26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1653, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 1654, limit := 1805 }) := by cbv

theorem functionIndex27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1654, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 1655, limit := 1805 }) := by cbv

theorem functionIndex28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1655, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 1656, limit := 1805 }) := by cbv

theorem functionIndex29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1656, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 1657, limit := 1805 }) := by cbv

theorem functionIndex30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1657, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 1658, limit := 1805 }) := by cbv

theorem functionIndex31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1658, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 1659, limit := 1805 }) := by cbv

#print axioms functionIndex31_decoded

end Project.EulerReconstructed.Artifact
