import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 553, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 554, limit := 603 }) := by cbv

#print axioms function16_decoded

theorem function17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 554, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 555, limit := 603 }) := by cbv

#print axioms function17_decoded

theorem function18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 555, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 556, limit := 603 }) := by cbv

#print axioms function18_decoded

theorem function19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 556, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 557, limit := 603 }) := by cbv

#print axioms function19_decoded

theorem function20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 557, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 558, limit := 603 }) := by cbv

#print axioms function20_decoded

theorem function21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 558, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 559, limit := 603 }) := by cbv

#print axioms function21_decoded

theorem function22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 559, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 560, limit := 603 }) := by cbv

#print axioms function22_decoded

theorem function23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 560, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 561, limit := 603 }) := by cbv

#print axioms function23_decoded

theorem function24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 561, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 562, limit := 603 }) := by cbv

#print axioms function24_decoded

theorem function25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 562, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 563, limit := 603 }) := by cbv

#print axioms function25_decoded

theorem function26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 563, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 564, limit := 603 }) := by cbv

#print axioms function26_decoded

theorem function27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 564, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 565, limit := 603 }) := by cbv

#print axioms function27_decoded

theorem function28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 565, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 566, limit := 603 }) := by cbv

#print axioms function28_decoded

theorem function29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 566, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 567, limit := 603 }) := by cbv

#print axioms function29_decoded

theorem function30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 567, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 568, limit := 603 }) := by cbv

#print axioms function30_decoded

theorem function31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 568, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 569, limit := 603 }) := by cbv

#print axioms function31_decoded


end Project.Gpt2QuantizedCached.Artifact
