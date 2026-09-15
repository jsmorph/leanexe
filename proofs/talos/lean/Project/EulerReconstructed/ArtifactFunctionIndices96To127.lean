import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex96_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1723, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[96]!, { bytes := artifactBytes, pos := 1724, limit := 1805 }) := by cbv

theorem functionIndex97_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1724, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[97]!, { bytes := artifactBytes, pos := 1725, limit := 1805 }) := by cbv

theorem functionIndex98_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1725, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[98]!, { bytes := artifactBytes, pos := 1726, limit := 1805 }) := by cbv

theorem functionIndex99_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1726, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[99]!, { bytes := artifactBytes, pos := 1727, limit := 1805 }) := by cbv

theorem functionIndex100_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1727, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[100]!, { bytes := artifactBytes, pos := 1728, limit := 1805 }) := by cbv

theorem functionIndex101_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1728, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[101]!, { bytes := artifactBytes, pos := 1729, limit := 1805 }) := by cbv

theorem functionIndex102_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1729, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[102]!, { bytes := artifactBytes, pos := 1730, limit := 1805 }) := by cbv

theorem functionIndex103_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1730, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[103]!, { bytes := artifactBytes, pos := 1731, limit := 1805 }) := by cbv

theorem functionIndex104_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1731, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[104]!, { bytes := artifactBytes, pos := 1732, limit := 1805 }) := by cbv

theorem functionIndex105_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1732, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[105]!, { bytes := artifactBytes, pos := 1733, limit := 1805 }) := by cbv

theorem functionIndex106_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1733, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[106]!, { bytes := artifactBytes, pos := 1734, limit := 1805 }) := by cbv

theorem functionIndex107_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1734, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[107]!, { bytes := artifactBytes, pos := 1735, limit := 1805 }) := by cbv

theorem functionIndex108_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1735, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[108]!, { bytes := artifactBytes, pos := 1736, limit := 1805 }) := by cbv

theorem functionIndex109_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1736, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[109]!, { bytes := artifactBytes, pos := 1737, limit := 1805 }) := by cbv

theorem functionIndex110_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1737, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[110]!, { bytes := artifactBytes, pos := 1738, limit := 1805 }) := by cbv

theorem functionIndex111_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1738, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[111]!, { bytes := artifactBytes, pos := 1739, limit := 1805 }) := by cbv

theorem functionIndex112_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1739, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[112]!, { bytes := artifactBytes, pos := 1740, limit := 1805 }) := by cbv

theorem functionIndex113_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1740, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[113]!, { bytes := artifactBytes, pos := 1741, limit := 1805 }) := by cbv

theorem functionIndex114_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1741, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[114]!, { bytes := artifactBytes, pos := 1742, limit := 1805 }) := by cbv

theorem functionIndex115_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1742, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[115]!, { bytes := artifactBytes, pos := 1743, limit := 1805 }) := by cbv

theorem functionIndex116_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1743, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[116]!, { bytes := artifactBytes, pos := 1744, limit := 1805 }) := by cbv

theorem functionIndex117_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1744, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[117]!, { bytes := artifactBytes, pos := 1745, limit := 1805 }) := by cbv

theorem functionIndex118_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1745, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[118]!, { bytes := artifactBytes, pos := 1746, limit := 1805 }) := by cbv

theorem functionIndex119_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1746, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[119]!, { bytes := artifactBytes, pos := 1747, limit := 1805 }) := by cbv

theorem functionIndex120_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1747, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[120]!, { bytes := artifactBytes, pos := 1748, limit := 1805 }) := by cbv

theorem functionIndex121_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1748, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[121]!, { bytes := artifactBytes, pos := 1749, limit := 1805 }) := by cbv

theorem functionIndex122_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1749, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[122]!, { bytes := artifactBytes, pos := 1750, limit := 1805 }) := by cbv

theorem functionIndex123_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1750, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[123]!, { bytes := artifactBytes, pos := 1751, limit := 1805 }) := by cbv

theorem functionIndex124_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1751, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[124]!, { bytes := artifactBytes, pos := 1752, limit := 1805 }) := by cbv

theorem functionIndex125_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1752, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[125]!, { bytes := artifactBytes, pos := 1753, limit := 1805 }) := by cbv

theorem functionIndex126_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1753, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[126]!, { bytes := artifactBytes, pos := 1754, limit := 1805 }) := by cbv

theorem functionIndex127_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1754, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[127]!, { bytes := artifactBytes, pos := 1755, limit := 1805 }) := by cbv

#print axioms functionIndex127_decoded

end Project.EulerReconstructed.Artifact
