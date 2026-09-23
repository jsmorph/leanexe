import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 537, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 538, limit := 603 }) := by cbv

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 538, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 539, limit := 603 }) := by cbv

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 539, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 540, limit := 603 }) := by cbv

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 540, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 541, limit := 603 }) := by cbv

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 541, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 542, limit := 603 }) := by cbv

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 542, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 543, limit := 603 }) := by cbv

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 543, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 544, limit := 603 }) := by cbv

theorem function7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 544, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 545, limit := 603 }) := by cbv

theorem function8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 545, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 546, limit := 603 }) := by cbv

theorem function9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 546, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 547, limit := 603 }) := by cbv

theorem function10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 547, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 548, limit := 603 }) := by cbv

theorem function11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 548, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 549, limit := 603 }) := by cbv

theorem function12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 549, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 550, limit := 603 }) := by cbv

theorem function13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 550, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 551, limit := 603 }) := by cbv

theorem function14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 551, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 552, limit := 603 }) := by cbv

theorem function15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 552, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 553, limit := 603 }) := by cbv


end Project.Gpt2QuantizedCached.Artifact
