import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart10

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex176_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2800, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[176]!, { bytes := artifactBytes, pos := 2802, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex176_decoded

theorem functionIndex177_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2802, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[177]!, { bytes := artifactBytes, pos := 2804, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex177_decoded

theorem functionIndex178_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2804, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[178]!, { bytes := artifactBytes, pos := 2806, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex178_decoded

theorem functionIndex179_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2806, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[179]!, { bytes := artifactBytes, pos := 2808, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex179_decoded

theorem functionIndex180_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2808, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[180]!, { bytes := artifactBytes, pos := 2810, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex180_decoded

theorem functionIndex181_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2810, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[181]!, { bytes := artifactBytes, pos := 2812, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex181_decoded

theorem functionIndex182_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2812, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[182]!, { bytes := artifactBytes, pos := 2814, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex182_decoded

theorem functionIndex183_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2814, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[183]!, { bytes := artifactBytes, pos := 2816, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex183_decoded

theorem functionIndex184_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2816, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[184]!, { bytes := artifactBytes, pos := 2818, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex184_decoded

theorem functionIndex185_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2818, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[185]!, { bytes := artifactBytes, pos := 2820, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex185_decoded

theorem functionIndex186_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2820, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[186]!, { bytes := artifactBytes, pos := 2822, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex186_decoded

theorem functionIndex187_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2822, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[187]!, { bytes := artifactBytes, pos := 2824, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex187_decoded

theorem functionIndex188_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2824, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[188]!, { bytes := artifactBytes, pos := 2826, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex188_decoded

theorem functionIndex189_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2826, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[189]!, { bytes := artifactBytes, pos := 2828, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex189_decoded

theorem functionIndex190_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2828, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[190]!, { bytes := artifactBytes, pos := 2830, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex190_decoded

theorem functionIndex191_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2830, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[191]!, { bytes := artifactBytes, pos := 2832, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex191_decoded

end Project.EulerCertificate.Artifact
