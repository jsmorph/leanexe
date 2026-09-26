import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function48_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 415, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 416, limit := 417 }) := by cbv

#print axioms function48_decoded

theorem function49_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 416, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 417, limit := 417 }) := by cbv

#print axioms function49_decoded


end Project.EulerOutwardGrid.Artifact
