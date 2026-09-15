import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex128_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1755, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[128]!, { bytes := artifactBytes, pos := 1757, limit := 1805 }) := by cbv

theorem functionIndex129_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1757, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[129]!, { bytes := artifactBytes, pos := 1759, limit := 1805 }) := by cbv

theorem functionIndex130_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1759, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[130]!, { bytes := artifactBytes, pos := 1761, limit := 1805 }) := by cbv

theorem functionIndex131_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1761, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[131]!, { bytes := artifactBytes, pos := 1763, limit := 1805 }) := by cbv

theorem functionIndex132_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1763, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[132]!, { bytes := artifactBytes, pos := 1765, limit := 1805 }) := by cbv

theorem functionIndex133_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1765, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[133]!, { bytes := artifactBytes, pos := 1767, limit := 1805 }) := by cbv

theorem functionIndex134_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1767, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[134]!, { bytes := artifactBytes, pos := 1769, limit := 1805 }) := by cbv

theorem functionIndex135_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1769, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[135]!, { bytes := artifactBytes, pos := 1771, limit := 1805 }) := by cbv

theorem functionIndex136_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1771, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[136]!, { bytes := artifactBytes, pos := 1773, limit := 1805 }) := by cbv

theorem functionIndex137_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1773, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[137]!, { bytes := artifactBytes, pos := 1775, limit := 1805 }) := by cbv

theorem functionIndex138_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1775, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[138]!, { bytes := artifactBytes, pos := 1777, limit := 1805 }) := by cbv

theorem functionIndex139_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1777, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[139]!, { bytes := artifactBytes, pos := 1779, limit := 1805 }) := by cbv

theorem functionIndex140_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1779, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[140]!, { bytes := artifactBytes, pos := 1781, limit := 1805 }) := by cbv

theorem functionIndex141_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1781, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[141]!, { bytes := artifactBytes, pos := 1783, limit := 1805 }) := by cbv

theorem functionIndex142_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1783, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[142]!, { bytes := artifactBytes, pos := 1785, limit := 1805 }) := by cbv

theorem functionIndex143_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1785, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[143]!, { bytes := artifactBytes, pos := 1787, limit := 1805 }) := by cbv

theorem functionIndex144_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1787, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[144]!, { bytes := artifactBytes, pos := 1789, limit := 1805 }) := by cbv

theorem functionIndex145_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1789, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[145]!, { bytes := artifactBytes, pos := 1791, limit := 1805 }) := by cbv

theorem functionIndex146_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1791, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[146]!, { bytes := artifactBytes, pos := 1793, limit := 1805 }) := by cbv

theorem functionIndex147_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1793, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[147]!, { bytes := artifactBytes, pos := 1795, limit := 1805 }) := by cbv

theorem functionIndex148_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1795, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[148]!, { bytes := artifactBytes, pos := 1797, limit := 1805 }) := by cbv

theorem functionIndex149_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1797, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[149]!, { bytes := artifactBytes, pos := 1799, limit := 1805 }) := by cbv

theorem functionIndex150_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1799, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[150]!, { bytes := artifactBytes, pos := 1801, limit := 1805 }) := by cbv

theorem functionIndex151_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1801, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[151]!, { bytes := artifactBytes, pos := 1803, limit := 1805 }) := by cbv

theorem functionIndex152_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 1803, limit := 1805 } =
      .ok (Cache.raw.functionTypeIndices[152]!, { bytes := artifactBytes, pos := 1805, limit := 1805 }) := by cbv

#print axioms functionIndex152_decoded

end Project.EulerReconstructed.Artifact
