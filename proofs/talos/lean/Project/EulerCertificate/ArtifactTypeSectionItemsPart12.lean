import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart11

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type192_decoded :
    funcType { bytes := artifactBytes, pos := 2559, limit := 2571 } =
      .ok (Cache.raw.types[192]!, { bytes := artifactBytes, pos := 2562, limit := 2571 }) := by cbv

#print axioms type192_decoded

theorem type193_decoded :
    funcType { bytes := artifactBytes, pos := 2562, limit := 2571 } =
      .ok (Cache.raw.types[193]!, { bytes := artifactBytes, pos := 2567, limit := 2571 }) := by cbv

#print axioms type193_decoded

theorem type194_decoded :
    funcType { bytes := artifactBytes, pos := 2567, limit := 2571 } =
      .ok (Cache.raw.types[194]!, { bytes := artifactBytes, pos := 2571, limit := 2571 }) := by cbv

#print axioms type194_decoded

end Project.EulerCertificate.Artifact
