import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart5

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex96_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2672, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[96]!, { bytes := artifactBytes, pos := 2673, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex96_decoded

theorem functionIndex97_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2673, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[97]!, { bytes := artifactBytes, pos := 2674, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex97_decoded

theorem functionIndex98_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2674, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[98]!, { bytes := artifactBytes, pos := 2675, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex98_decoded

theorem functionIndex99_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2675, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[99]!, { bytes := artifactBytes, pos := 2676, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex99_decoded

theorem functionIndex100_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2676, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[100]!, { bytes := artifactBytes, pos := 2677, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex100_decoded

theorem functionIndex101_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2677, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[101]!, { bytes := artifactBytes, pos := 2678, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex101_decoded

theorem functionIndex102_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2678, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[102]!, { bytes := artifactBytes, pos := 2679, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex102_decoded

theorem functionIndex103_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2679, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[103]!, { bytes := artifactBytes, pos := 2680, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex103_decoded

theorem functionIndex104_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2680, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[104]!, { bytes := artifactBytes, pos := 2681, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex104_decoded

theorem functionIndex105_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2681, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[105]!, { bytes := artifactBytes, pos := 2682, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex105_decoded

theorem functionIndex106_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2682, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[106]!, { bytes := artifactBytes, pos := 2683, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex106_decoded

theorem functionIndex107_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2683, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[107]!, { bytes := artifactBytes, pos := 2684, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex107_decoded

theorem functionIndex108_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2684, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[108]!, { bytes := artifactBytes, pos := 2685, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex108_decoded

theorem functionIndex109_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2685, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[109]!, { bytes := artifactBytes, pos := 2686, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex109_decoded

theorem functionIndex110_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2686, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[110]!, { bytes := artifactBytes, pos := 2687, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex110_decoded

theorem functionIndex111_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2687, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[111]!, { bytes := artifactBytes, pos := 2688, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex111_decoded

end Project.EulerCertificate.Artifact
