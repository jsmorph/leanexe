import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart4

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex80_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2656, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[80]!, { bytes := artifactBytes, pos := 2657, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex80_decoded

theorem functionIndex81_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2657, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[81]!, { bytes := artifactBytes, pos := 2658, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex81_decoded

theorem functionIndex82_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2658, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[82]!, { bytes := artifactBytes, pos := 2659, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex82_decoded

theorem functionIndex83_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2659, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[83]!, { bytes := artifactBytes, pos := 2660, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex83_decoded

theorem functionIndex84_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2660, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[84]!, { bytes := artifactBytes, pos := 2661, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex84_decoded

theorem functionIndex85_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2661, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[85]!, { bytes := artifactBytes, pos := 2662, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex85_decoded

theorem functionIndex86_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2662, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[86]!, { bytes := artifactBytes, pos := 2663, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex86_decoded

theorem functionIndex87_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2663, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[87]!, { bytes := artifactBytes, pos := 2664, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex87_decoded

theorem functionIndex88_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2664, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[88]!, { bytes := artifactBytes, pos := 2665, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex88_decoded

theorem functionIndex89_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2665, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[89]!, { bytes := artifactBytes, pos := 2666, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex89_decoded

theorem functionIndex90_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2666, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[90]!, { bytes := artifactBytes, pos := 2667, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex90_decoded

theorem functionIndex91_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2667, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[91]!, { bytes := artifactBytes, pos := 2668, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex91_decoded

theorem functionIndex92_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2668, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[92]!, { bytes := artifactBytes, pos := 2669, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex92_decoded

theorem functionIndex93_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2669, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[93]!, { bytes := artifactBytes, pos := 2670, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex93_decoded

theorem functionIndex94_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2670, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[94]!, { bytes := artifactBytes, pos := 2671, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex94_decoded

theorem functionIndex95_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2671, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[95]!, { bytes := artifactBytes, pos := 2672, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex95_decoded

end Project.EulerCertificate.Artifact
