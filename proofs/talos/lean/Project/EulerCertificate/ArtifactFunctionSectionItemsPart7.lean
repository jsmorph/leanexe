import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart6

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex112_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2688, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[112]!, { bytes := artifactBytes, pos := 2689, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex112_decoded

theorem functionIndex113_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2689, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[113]!, { bytes := artifactBytes, pos := 2690, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex113_decoded

theorem functionIndex114_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2690, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[114]!, { bytes := artifactBytes, pos := 2691, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex114_decoded

theorem functionIndex115_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2691, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[115]!, { bytes := artifactBytes, pos := 2692, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex115_decoded

theorem functionIndex116_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2692, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[116]!, { bytes := artifactBytes, pos := 2693, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex116_decoded

theorem functionIndex117_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2693, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[117]!, { bytes := artifactBytes, pos := 2694, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex117_decoded

theorem functionIndex118_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2694, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[118]!, { bytes := artifactBytes, pos := 2695, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex118_decoded

theorem functionIndex119_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2695, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[119]!, { bytes := artifactBytes, pos := 2696, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex119_decoded

theorem functionIndex120_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2696, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[120]!, { bytes := artifactBytes, pos := 2697, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex120_decoded

theorem functionIndex121_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2697, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[121]!, { bytes := artifactBytes, pos := 2698, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex121_decoded

theorem functionIndex122_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2698, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[122]!, { bytes := artifactBytes, pos := 2699, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex122_decoded

theorem functionIndex123_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2699, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[123]!, { bytes := artifactBytes, pos := 2700, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex123_decoded

theorem functionIndex124_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2700, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[124]!, { bytes := artifactBytes, pos := 2701, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex124_decoded

theorem functionIndex125_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2701, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[125]!, { bytes := artifactBytes, pos := 2702, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex125_decoded

theorem functionIndex126_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2702, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[126]!, { bytes := artifactBytes, pos := 2703, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex126_decoded

theorem functionIndex127_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2703, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[127]!, { bytes := artifactBytes, pos := 2704, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex127_decoded

end Project.EulerCertificate.Artifact
