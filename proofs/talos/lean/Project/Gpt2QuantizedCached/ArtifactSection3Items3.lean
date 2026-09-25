import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function48_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 585, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 586, limit := 603 }) := by cbv

#print axioms function48_decoded

theorem function49_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 586, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 587, limit := 603 }) := by cbv

#print axioms function49_decoded

theorem function50_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 587, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[50]!, { bytes := artifactBytes, pos := 588, limit := 603 }) := by cbv

#print axioms function50_decoded

theorem function51_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 588, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[51]!, { bytes := artifactBytes, pos := 589, limit := 603 }) := by cbv

#print axioms function51_decoded

theorem function52_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 589, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[52]!, { bytes := artifactBytes, pos := 590, limit := 603 }) := by cbv

#print axioms function52_decoded

theorem function53_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 590, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[53]!, { bytes := artifactBytes, pos := 591, limit := 603 }) := by cbv

#print axioms function53_decoded

theorem function54_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 591, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[54]!, { bytes := artifactBytes, pos := 592, limit := 603 }) := by cbv

#print axioms function54_decoded

theorem function55_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 592, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[55]!, { bytes := artifactBytes, pos := 593, limit := 603 }) := by cbv

#print axioms function55_decoded

theorem function56_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 593, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[56]!, { bytes := artifactBytes, pos := 594, limit := 603 }) := by cbv

#print axioms function56_decoded

theorem function57_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 594, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[57]!, { bytes := artifactBytes, pos := 595, limit := 603 }) := by cbv

#print axioms function57_decoded

theorem function58_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 595, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[58]!, { bytes := artifactBytes, pos := 596, limit := 603 }) := by cbv

#print axioms function58_decoded

theorem function59_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 596, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[59]!, { bytes := artifactBytes, pos := 597, limit := 603 }) := by cbv

#print axioms function59_decoded

theorem function60_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 597, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[60]!, { bytes := artifactBytes, pos := 598, limit := 603 }) := by cbv

#print axioms function60_decoded

theorem function61_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 598, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[61]!, { bytes := artifactBytes, pos := 599, limit := 603 }) := by cbv

#print axioms function61_decoded

theorem function62_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 599, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[62]!, { bytes := artifactBytes, pos := 600, limit := 603 }) := by cbv

#print axioms function62_decoded

theorem function63_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 600, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[63]!, { bytes := artifactBytes, pos := 601, limit := 603 }) := by cbv

#print axioms function63_decoded


end Project.Gpt2QuantizedCached.Artifact
