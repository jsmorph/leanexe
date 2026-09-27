import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 454, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 455, limit := 462 }) := by cbv

#print axioms function32_decoded

theorem function33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 455, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 456, limit := 462 }) := by cbv

#print axioms function33_decoded

theorem function34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 456, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 457, limit := 462 }) := by cbv

#print axioms function34_decoded

theorem function35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 457, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 458, limit := 462 }) := by cbv

#print axioms function35_decoded

theorem function36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 458, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 459, limit := 462 }) := by cbv

#print axioms function36_decoded

theorem function37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 459, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 460, limit := 462 }) := by cbv

#print axioms function37_decoded

theorem function38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 460, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 461, limit := 462 }) := by cbv

#print axioms function38_decoded

theorem function39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 461, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 462, limit := 462 }) := by cbv

#print axioms function39_decoded


end Project.Beck.Artifact
