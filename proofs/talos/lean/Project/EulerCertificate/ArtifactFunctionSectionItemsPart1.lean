import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2592, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 2593, limit := 2838 }) := by cbv

#print axioms functionIndex16_decoded

theorem functionIndex17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2593, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 2594, limit := 2838 }) := by cbv

#print axioms functionIndex17_decoded

theorem functionIndex18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2594, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 2595, limit := 2838 }) := by cbv

#print axioms functionIndex18_decoded

theorem functionIndex19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2595, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 2596, limit := 2838 }) := by cbv

#print axioms functionIndex19_decoded

theorem functionIndex20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2596, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 2597, limit := 2838 }) := by cbv

#print axioms functionIndex20_decoded

theorem functionIndex21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2597, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 2598, limit := 2838 }) := by cbv

#print axioms functionIndex21_decoded

theorem functionIndex22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2598, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 2599, limit := 2838 }) := by cbv

#print axioms functionIndex22_decoded

theorem functionIndex23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2599, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 2600, limit := 2838 }) := by cbv

#print axioms functionIndex23_decoded

theorem functionIndex24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2600, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 2601, limit := 2838 }) := by cbv

#print axioms functionIndex24_decoded

theorem functionIndex25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2601, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 2602, limit := 2838 }) := by cbv

#print axioms functionIndex25_decoded

theorem functionIndex26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2602, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 2603, limit := 2838 }) := by cbv

#print axioms functionIndex26_decoded

theorem functionIndex27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2603, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 2604, limit := 2838 }) := by cbv

#print axioms functionIndex27_decoded

theorem functionIndex28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2604, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 2605, limit := 2838 }) := by cbv

#print axioms functionIndex28_decoded

theorem functionIndex29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2605, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 2606, limit := 2838 }) := by cbv

#print axioms functionIndex29_decoded

theorem functionIndex30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2606, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 2607, limit := 2838 }) := by cbv

#print axioms functionIndex30_decoded

theorem functionIndex31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2607, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 2608, limit := 2838 }) := by cbv

#print axioms functionIndex31_decoded

end Project.EulerCertificate.Artifact
