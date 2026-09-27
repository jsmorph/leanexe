import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactIndexLookup
import Project.Artifact.Binary.CodeParts

open Wasm.Binary Project.EulerCertificate.Artifact

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000
set_option trace.profiler true
set_option trace.profiler.threshold 250
set_option pp.maxDepth 6
set_option pp.maxSteps 300

namespace EulerCertificateIndexProfile

theorem baseline :
    Leb.u32 { bytes := artifactBytes, pos := 2576, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[0]!,
        { bytes := artifactBytes, pos := 2577, limit := 2838 }) := by
  cbv

#print axioms baseline

theorem fieldEquality :
    Leb.u32 { bytes := artifactBytes, pos := 2576, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[0]!,
        { bytes := artifactBytes, pos := 2577, limit := 2838 }) := by
  rw [functionTypeIndices_eq]
  cbv

#print axioms fieldEquality
end EulerCertificateIndexProfile
