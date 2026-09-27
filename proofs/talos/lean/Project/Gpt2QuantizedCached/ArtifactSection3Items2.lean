import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 569, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 570, limit := 603 }) := by cbv

#print axioms function32_decoded

theorem function33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 570, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 571, limit := 603 }) := by cbv

#print axioms function33_decoded

theorem function34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 571, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 572, limit := 603 }) := by cbv

#print axioms function34_decoded

theorem function35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 572, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 573, limit := 603 }) := by cbv

#print axioms function35_decoded

theorem function36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 573, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 574, limit := 603 }) := by cbv

#print axioms function36_decoded

theorem function37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 574, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 575, limit := 603 }) := by cbv

#print axioms function37_decoded

theorem function38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 575, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 576, limit := 603 }) := by cbv

#print axioms function38_decoded

theorem function39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 576, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 577, limit := 603 }) := by cbv

#print axioms function39_decoded

theorem function40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 577, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 578, limit := 603 }) := by cbv

#print axioms function40_decoded

theorem function41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 578, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 579, limit := 603 }) := by cbv

#print axioms function41_decoded

theorem function42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 579, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 580, limit := 603 }) := by cbv

#print axioms function42_decoded

theorem function43_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 580, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 581, limit := 603 }) := by cbv

#print axioms function43_decoded

theorem function44_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 581, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 582, limit := 603 }) := by cbv

#print axioms function44_decoded

theorem function45_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 582, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 583, limit := 603 }) := by cbv

#print axioms function45_decoded

theorem function46_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 583, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 584, limit := 603 }) := by cbv

#print axioms function46_decoded

theorem function47_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 584, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 585, limit := 603 }) := by cbv

#print axioms function47_decoded


end Project.Gpt2QuantizedCached.Artifact
