import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1659, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 1660, limit := 1805 }) := by cbv

theorem functionIndex33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1660, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 1661, limit := 1805 }) := by cbv

theorem functionIndex34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1661, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 1662, limit := 1805 }) := by cbv

theorem functionIndex35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1662, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 1663, limit := 1805 }) := by cbv

theorem functionIndex36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1663, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 1664, limit := 1805 }) := by cbv

theorem functionIndex37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1664, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 1665, limit := 1805 }) := by cbv

theorem functionIndex38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1665, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 1666, limit := 1805 }) := by cbv

theorem functionIndex39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1666, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 1667, limit := 1805 }) := by cbv

theorem functionIndex40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1667, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 1668, limit := 1805 }) := by cbv

theorem functionIndex41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1668, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 1669, limit := 1805 }) := by cbv

theorem functionIndex42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1669, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 1670, limit := 1805 }) := by cbv

theorem functionIndex43_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1670, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 1671, limit := 1805 }) := by cbv

theorem functionIndex44_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1671, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 1672, limit := 1805 }) := by cbv

theorem functionIndex45_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1672, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 1673, limit := 1805 }) := by cbv

theorem functionIndex46_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1673, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 1674, limit := 1805 }) := by cbv

theorem functionIndex47_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1674, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 1675, limit := 1805 }) := by cbv

theorem functionIndex48_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1675, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 1676, limit := 1805 }) := by cbv

theorem functionIndex49_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1676, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 1677, limit := 1805 }) := by cbv

theorem functionIndex50_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1677, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[50]!, { bytes := artifactBytes, pos := 1678, limit := 1805 }) := by cbv

theorem functionIndex51_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1678, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[51]!, { bytes := artifactBytes, pos := 1679, limit := 1805 }) := by cbv

theorem functionIndex52_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1679, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[52]!, { bytes := artifactBytes, pos := 1680, limit := 1805 }) := by cbv

theorem functionIndex53_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1680, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[53]!, { bytes := artifactBytes, pos := 1681, limit := 1805 }) := by cbv

theorem functionIndex54_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1681, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[54]!, { bytes := artifactBytes, pos := 1682, limit := 1805 }) := by cbv

theorem functionIndex55_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1682, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[55]!, { bytes := artifactBytes, pos := 1683, limit := 1805 }) := by cbv

theorem functionIndex56_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1683, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[56]!, { bytes := artifactBytes, pos := 1684, limit := 1805 }) := by cbv

theorem functionIndex57_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1684, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[57]!, { bytes := artifactBytes, pos := 1685, limit := 1805 }) := by cbv

theorem functionIndex58_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1685, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[58]!, { bytes := artifactBytes, pos := 1686, limit := 1805 }) := by cbv

theorem functionIndex59_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1686, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[59]!, { bytes := artifactBytes, pos := 1687, limit := 1805 }) := by cbv

theorem functionIndex60_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1687, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[60]!, { bytes := artifactBytes, pos := 1688, limit := 1805 }) := by cbv

theorem functionIndex61_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1688, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[61]!, { bytes := artifactBytes, pos := 1689, limit := 1805 }) := by cbv

theorem functionIndex62_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1689, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[62]!, { bytes := artifactBytes, pos := 1690, limit := 1805 }) := by cbv

theorem functionIndex63_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1690, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[63]!, { bytes := artifactBytes, pos := 1691, limit := 1805 }) := by cbv

#print axioms functionIndex63_decoded

end Project.EulerReconstructed.Artifact
