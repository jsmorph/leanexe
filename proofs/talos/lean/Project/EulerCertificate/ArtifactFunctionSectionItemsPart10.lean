import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart9

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex160_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2768, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[160]!, { bytes := artifactBytes, pos := 2770, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex160_decoded

theorem functionIndex161_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2770, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[161]!, { bytes := artifactBytes, pos := 2772, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex161_decoded

theorem functionIndex162_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2772, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[162]!, { bytes := artifactBytes, pos := 2774, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex162_decoded

theorem functionIndex163_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2774, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[163]!, { bytes := artifactBytes, pos := 2776, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex163_decoded

theorem functionIndex164_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2776, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[164]!, { bytes := artifactBytes, pos := 2778, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex164_decoded

theorem functionIndex165_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2778, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[165]!, { bytes := artifactBytes, pos := 2780, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex165_decoded

theorem functionIndex166_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2780, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[166]!, { bytes := artifactBytes, pos := 2782, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex166_decoded

theorem functionIndex167_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2782, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[167]!, { bytes := artifactBytes, pos := 2784, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex167_decoded

theorem functionIndex168_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2784, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[168]!, { bytes := artifactBytes, pos := 2786, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex168_decoded

theorem functionIndex169_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2786, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[169]!, { bytes := artifactBytes, pos := 2788, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex169_decoded

theorem functionIndex170_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2788, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[170]!, { bytes := artifactBytes, pos := 2790, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex170_decoded

theorem functionIndex171_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2790, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[171]!, { bytes := artifactBytes, pos := 2792, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex171_decoded

theorem functionIndex172_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2792, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[172]!, { bytes := artifactBytes, pos := 2794, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex172_decoded

theorem functionIndex173_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2794, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[173]!, { bytes := artifactBytes, pos := 2796, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex173_decoded

theorem functionIndex174_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2796, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[174]!, { bytes := artifactBytes, pos := 2798, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex174_decoded

theorem functionIndex175_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2798, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[175]!, { bytes := artifactBytes, pos := 2800, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex175_decoded

end Project.EulerCertificate.Artifact
