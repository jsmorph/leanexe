import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactIndexLookup
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart11

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex192_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2832, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[192]!, { bytes := artifactBytes, pos := 2834, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex192_decoded

theorem functionIndex193_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2834, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[193]!, { bytes := artifactBytes, pos := 2836, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex193_decoded

theorem functionIndex194_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2836, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[194]!, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms functionIndex194_decoded

end Project.EulerCertificate.Artifact
