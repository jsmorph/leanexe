import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart3

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex64_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2640, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[64]!, { bytes := artifactBytes, pos := 2641, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex64_decoded

theorem functionIndex65_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2641, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[65]!, { bytes := artifactBytes, pos := 2642, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex65_decoded

theorem functionIndex66_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2642, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[66]!, { bytes := artifactBytes, pos := 2643, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex66_decoded

theorem functionIndex67_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2643, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[67]!, { bytes := artifactBytes, pos := 2644, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex67_decoded

theorem functionIndex68_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2644, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[68]!, { bytes := artifactBytes, pos := 2645, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex68_decoded

theorem functionIndex69_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2645, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[69]!, { bytes := artifactBytes, pos := 2646, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex69_decoded

theorem functionIndex70_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2646, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[70]!, { bytes := artifactBytes, pos := 2647, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex70_decoded

theorem functionIndex71_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2647, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[71]!, { bytes := artifactBytes, pos := 2648, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex71_decoded

theorem functionIndex72_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2648, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[72]!, { bytes := artifactBytes, pos := 2649, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex72_decoded

theorem functionIndex73_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2649, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[73]!, { bytes := artifactBytes, pos := 2650, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex73_decoded

theorem functionIndex74_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2650, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[74]!, { bytes := artifactBytes, pos := 2651, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex74_decoded

theorem functionIndex75_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2651, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[75]!, { bytes := artifactBytes, pos := 2652, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex75_decoded

theorem functionIndex76_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2652, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[76]!, { bytes := artifactBytes, pos := 2653, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex76_decoded

theorem functionIndex77_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2653, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[77]!, { bytes := artifactBytes, pos := 2654, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex77_decoded

theorem functionIndex78_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2654, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[78]!, { bytes := artifactBytes, pos := 2655, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex78_decoded

theorem functionIndex79_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2655, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[79]!, { bytes := artifactBytes, pos := 2656, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex79_decoded

end Project.EulerCertificate.Artifact
