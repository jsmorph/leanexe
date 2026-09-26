import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 399, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 400, limit := 417 }) := by cbv

#print axioms function32_decoded

theorem function33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 400, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 401, limit := 417 }) := by cbv

#print axioms function33_decoded

theorem function34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 401, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 402, limit := 417 }) := by cbv

#print axioms function34_decoded

theorem function35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 402, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 403, limit := 417 }) := by cbv

#print axioms function35_decoded

theorem function36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 403, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 404, limit := 417 }) := by cbv

#print axioms function36_decoded

theorem function37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 404, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 405, limit := 417 }) := by cbv

#print axioms function37_decoded

theorem function38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 405, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 406, limit := 417 }) := by cbv

#print axioms function38_decoded

theorem function39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 406, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 407, limit := 417 }) := by cbv

#print axioms function39_decoded

theorem function40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 407, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 408, limit := 417 }) := by cbv

#print axioms function40_decoded

theorem function41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 408, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 409, limit := 417 }) := by cbv

#print axioms function41_decoded

theorem function42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 409, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 410, limit := 417 }) := by cbv

#print axioms function42_decoded

theorem function43_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 410, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 411, limit := 417 }) := by cbv

#print axioms function43_decoded

theorem function44_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 411, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 412, limit := 417 }) := by cbv

#print axioms function44_decoded

theorem function45_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 412, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 413, limit := 417 }) := by cbv

#print axioms function45_decoded

theorem function46_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 413, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 414, limit := 417 }) := by cbv

#print axioms function46_decoded

theorem function47_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 414, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 415, limit := 417 }) := by cbv

#print axioms function47_decoded


end Project.EulerOutwardGrid.Artifact
