import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 367, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 368, limit := 417 }) := by cbv

#print axioms function0_decoded

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 368, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 369, limit := 417 }) := by cbv

#print axioms function1_decoded

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 369, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 370, limit := 417 }) := by cbv

#print axioms function2_decoded

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 370, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 371, limit := 417 }) := by cbv

#print axioms function3_decoded

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 371, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 372, limit := 417 }) := by cbv

#print axioms function4_decoded

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 372, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 373, limit := 417 }) := by cbv

#print axioms function5_decoded

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 373, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 374, limit := 417 }) := by cbv

#print axioms function6_decoded

theorem function7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 374, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 375, limit := 417 }) := by cbv

#print axioms function7_decoded

theorem function8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 375, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 376, limit := 417 }) := by cbv

#print axioms function8_decoded

theorem function9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 376, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 377, limit := 417 }) := by cbv

#print axioms function9_decoded

theorem function10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 377, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 378, limit := 417 }) := by cbv

#print axioms function10_decoded

theorem function11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 378, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 379, limit := 417 }) := by cbv

#print axioms function11_decoded

theorem function12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 379, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 380, limit := 417 }) := by cbv

#print axioms function12_decoded

theorem function13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 380, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 381, limit := 417 }) := by cbv

#print axioms function13_decoded

theorem function14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 381, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 382, limit := 417 }) := by cbv

#print axioms function14_decoded

theorem function15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 382, limit := 417 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 383, limit := 417 }) := by cbv

#print axioms function15_decoded


end Project.EulerOutwardGrid.Artifact
