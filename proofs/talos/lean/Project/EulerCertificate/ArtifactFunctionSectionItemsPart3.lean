import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart2

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex48_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2624, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 2625, limit := 2838 }) := by cbv

#print axioms functionIndex48_decoded

theorem functionIndex49_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2625, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 2626, limit := 2838 }) := by cbv

#print axioms functionIndex49_decoded

theorem functionIndex50_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2626, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[50]!, { bytes := artifactBytes, pos := 2627, limit := 2838 }) := by cbv

#print axioms functionIndex50_decoded

theorem functionIndex51_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2627, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[51]!, { bytes := artifactBytes, pos := 2628, limit := 2838 }) := by cbv

#print axioms functionIndex51_decoded

theorem functionIndex52_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2628, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[52]!, { bytes := artifactBytes, pos := 2629, limit := 2838 }) := by cbv

#print axioms functionIndex52_decoded

theorem functionIndex53_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2629, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[53]!, { bytes := artifactBytes, pos := 2630, limit := 2838 }) := by cbv

#print axioms functionIndex53_decoded

theorem functionIndex54_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2630, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[54]!, { bytes := artifactBytes, pos := 2631, limit := 2838 }) := by cbv

#print axioms functionIndex54_decoded

theorem functionIndex55_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2631, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[55]!, { bytes := artifactBytes, pos := 2632, limit := 2838 }) := by cbv

#print axioms functionIndex55_decoded

theorem functionIndex56_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2632, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[56]!, { bytes := artifactBytes, pos := 2633, limit := 2838 }) := by cbv

#print axioms functionIndex56_decoded

theorem functionIndex57_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2633, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[57]!, { bytes := artifactBytes, pos := 2634, limit := 2838 }) := by cbv

#print axioms functionIndex57_decoded

theorem functionIndex58_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2634, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[58]!, { bytes := artifactBytes, pos := 2635, limit := 2838 }) := by cbv

#print axioms functionIndex58_decoded

theorem functionIndex59_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2635, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[59]!, { bytes := artifactBytes, pos := 2636, limit := 2838 }) := by cbv

#print axioms functionIndex59_decoded

theorem functionIndex60_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2636, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[60]!, { bytes := artifactBytes, pos := 2637, limit := 2838 }) := by cbv

#print axioms functionIndex60_decoded

theorem functionIndex61_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2637, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[61]!, { bytes := artifactBytes, pos := 2638, limit := 2838 }) := by cbv

#print axioms functionIndex61_decoded

theorem functionIndex62_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2638, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[62]!, { bytes := artifactBytes, pos := 2639, limit := 2838 }) := by cbv

#print axioms functionIndex62_decoded

theorem functionIndex63_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2639, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[63]!, { bytes := artifactBytes, pos := 2640, limit := 2838 }) := by cbv

#print axioms functionIndex63_decoded

end Project.EulerCertificate.Artifact
