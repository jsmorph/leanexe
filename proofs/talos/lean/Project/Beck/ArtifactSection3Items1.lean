import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 438, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 439, limit := 462 }) := by cbv

#print axioms function16_decoded

theorem function17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 439, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 440, limit := 462 }) := by cbv

#print axioms function17_decoded

theorem function18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 440, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 441, limit := 462 }) := by cbv

#print axioms function18_decoded

theorem function19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 441, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 442, limit := 462 }) := by cbv

#print axioms function19_decoded

theorem function20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 442, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 443, limit := 462 }) := by cbv

#print axioms function20_decoded

theorem function21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 443, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 444, limit := 462 }) := by cbv

#print axioms function21_decoded

theorem function22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 444, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 445, limit := 462 }) := by cbv

#print axioms function22_decoded

theorem function23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 445, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 446, limit := 462 }) := by cbv

#print axioms function23_decoded

theorem function24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 446, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 447, limit := 462 }) := by cbv

#print axioms function24_decoded

theorem function25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 447, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 448, limit := 462 }) := by cbv

#print axioms function25_decoded

theorem function26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 448, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 449, limit := 462 }) := by cbv

#print axioms function26_decoded

theorem function27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 449, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 450, limit := 462 }) := by cbv

#print axioms function27_decoded

theorem function28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 450, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 451, limit := 462 }) := by cbv

#print axioms function28_decoded

theorem function29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 451, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 452, limit := 462 }) := by cbv

#print axioms function29_decoded

theorem function30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 452, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 453, limit := 462 }) := by cbv

#print axioms function30_decoded

theorem function31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 453, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 454, limit := 462 }) := by cbv

#print axioms function31_decoded


end Project.Beck.Artifact
