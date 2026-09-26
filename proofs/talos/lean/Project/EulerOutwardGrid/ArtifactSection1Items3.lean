import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type48_decoded :
    funcType { bytes := artifactBytes, pos := 355, limit := 364 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 360, limit := 364 }) := by cbv

#print axioms type48_decoded

theorem type49_decoded :
    funcType { bytes := artifactBytes, pos := 360, limit := 364 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 364, limit := 364 }) := by cbv

#print axioms type49_decoded


end Project.EulerOutwardGrid.Artifact
