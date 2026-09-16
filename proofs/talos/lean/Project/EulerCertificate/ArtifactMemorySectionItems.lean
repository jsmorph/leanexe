import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem memory0_decoded :
    memoryType { bytes := artifactBytes, pos := 2841, limit := 2843 } =
      .ok (Cache.raw.memories[0]!, { bytes := artifactBytes, pos := 2843, limit := 2843 }) := by cbv

#print axioms memory0_decoded

end Project.EulerCertificate.Artifact
