import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart7

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex128_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2704, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[128]!, { bytes := artifactBytes, pos := 2706, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex128_decoded

theorem functionIndex129_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2706, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[129]!, { bytes := artifactBytes, pos := 2708, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex129_decoded

theorem functionIndex130_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2708, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[130]!, { bytes := artifactBytes, pos := 2710, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex130_decoded

theorem functionIndex131_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2710, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[131]!, { bytes := artifactBytes, pos := 2712, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex131_decoded

theorem functionIndex132_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2712, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[132]!, { bytes := artifactBytes, pos := 2714, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex132_decoded

theorem functionIndex133_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2714, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[133]!, { bytes := artifactBytes, pos := 2716, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex133_decoded

theorem functionIndex134_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2716, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[134]!, { bytes := artifactBytes, pos := 2718, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex134_decoded

theorem functionIndex135_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2718, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[135]!, { bytes := artifactBytes, pos := 2720, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex135_decoded

theorem functionIndex136_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2720, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[136]!, { bytes := artifactBytes, pos := 2722, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex136_decoded

theorem functionIndex137_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2722, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[137]!, { bytes := artifactBytes, pos := 2724, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex137_decoded

theorem functionIndex138_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2724, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[138]!, { bytes := artifactBytes, pos := 2726, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex138_decoded

theorem functionIndex139_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2726, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[139]!, { bytes := artifactBytes, pos := 2728, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex139_decoded

theorem functionIndex140_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2728, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[140]!, { bytes := artifactBytes, pos := 2730, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex140_decoded

theorem functionIndex141_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2730, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[141]!, { bytes := artifactBytes, pos := 2732, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex141_decoded

theorem functionIndex142_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2732, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[142]!, { bytes := artifactBytes, pos := 2734, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex142_decoded

theorem functionIndex143_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2734, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[143]!, { bytes := artifactBytes, pos := 2736, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex143_decoded

end Project.EulerCertificate.Artifact
