import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 422, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 423, limit := 462 }) := by cbv

#print axioms function0_decoded

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 423, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 424, limit := 462 }) := by cbv

#print axioms function1_decoded

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 424, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 425, limit := 462 }) := by cbv

#print axioms function2_decoded

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 425, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 426, limit := 462 }) := by cbv

#print axioms function3_decoded

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 426, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 427, limit := 462 }) := by cbv

#print axioms function4_decoded

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 427, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 428, limit := 462 }) := by cbv

#print axioms function5_decoded

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 428, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 429, limit := 462 }) := by cbv

#print axioms function6_decoded

theorem function7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 429, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 430, limit := 462 }) := by cbv

#print axioms function7_decoded

theorem function8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 430, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 431, limit := 462 }) := by cbv

#print axioms function8_decoded

theorem function9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 431, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 432, limit := 462 }) := by cbv

#print axioms function9_decoded

theorem function10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 432, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 433, limit := 462 }) := by cbv

#print axioms function10_decoded

theorem function11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 433, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 434, limit := 462 }) := by cbv

#print axioms function11_decoded

theorem function12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 434, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 435, limit := 462 }) := by cbv

#print axioms function12_decoded

theorem function13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 435, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 436, limit := 462 }) := by cbv

#print axioms function13_decoded

theorem function14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 436, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 437, limit := 462 }) := by cbv

#print axioms function14_decoded

theorem function15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 437, limit := 462 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 438, limit := 462 }) := by cbv

#print axioms function15_decoded


end Project.Beck.Artifact
