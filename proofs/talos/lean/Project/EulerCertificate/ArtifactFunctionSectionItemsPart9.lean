import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart8

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex144_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2736, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[144]!, { bytes := artifactBytes, pos := 2738, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex144_decoded

theorem functionIndex145_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2738, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[145]!, { bytes := artifactBytes, pos := 2740, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex145_decoded

theorem functionIndex146_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2740, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[146]!, { bytes := artifactBytes, pos := 2742, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex146_decoded

theorem functionIndex147_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2742, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[147]!, { bytes := artifactBytes, pos := 2744, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex147_decoded

theorem functionIndex148_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2744, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[148]!, { bytes := artifactBytes, pos := 2746, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex148_decoded

theorem functionIndex149_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2746, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[149]!, { bytes := artifactBytes, pos := 2748, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex149_decoded

theorem functionIndex150_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2748, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[150]!, { bytes := artifactBytes, pos := 2750, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex150_decoded

theorem functionIndex151_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2750, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[151]!, { bytes := artifactBytes, pos := 2752, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex151_decoded

theorem functionIndex152_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2752, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[152]!, { bytes := artifactBytes, pos := 2754, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex152_decoded

theorem functionIndex153_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2754, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[153]!, { bytes := artifactBytes, pos := 2756, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex153_decoded

theorem functionIndex154_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2756, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[154]!, { bytes := artifactBytes, pos := 2758, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex154_decoded

theorem functionIndex155_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2758, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[155]!, { bytes := artifactBytes, pos := 2760, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex155_decoded

theorem functionIndex156_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2760, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[156]!, { bytes := artifactBytes, pos := 2762, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex156_decoded

theorem functionIndex157_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2762, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[157]!, { bytes := artifactBytes, pos := 2764, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex157_decoded

theorem functionIndex158_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2764, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[158]!, { bytes := artifactBytes, pos := 2766, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex158_decoded

theorem functionIndex159_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2766, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[159]!, { bytes := artifactBytes, pos := 2768, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex159_decoded

end Project.EulerCertificate.Artifact
