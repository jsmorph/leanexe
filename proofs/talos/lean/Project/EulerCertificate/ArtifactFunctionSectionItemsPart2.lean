import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactFunctionSectionItemsPart1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2608, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 2609, limit := 2838 }) := by cbv

#print axioms functionIndex32_decoded

theorem functionIndex33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2609, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 2610, limit := 2838 }) := by cbv

#print axioms functionIndex33_decoded

theorem functionIndex34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2610, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 2611, limit := 2838 }) := by cbv

#print axioms functionIndex34_decoded

theorem functionIndex35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2611, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 2612, limit := 2838 }) := by cbv

#print axioms functionIndex35_decoded

theorem functionIndex36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2612, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 2613, limit := 2838 }) := by cbv

#print axioms functionIndex36_decoded

theorem functionIndex37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2613, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 2614, limit := 2838 }) := by cbv

#print axioms functionIndex37_decoded

theorem functionIndex38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2614, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 2615, limit := 2838 }) := by cbv

#print axioms functionIndex38_decoded

theorem functionIndex39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2615, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 2616, limit := 2838 }) := by cbv

#print axioms functionIndex39_decoded

theorem functionIndex40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2616, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 2617, limit := 2838 }) := by cbv

#print axioms functionIndex40_decoded

theorem functionIndex41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2617, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 2618, limit := 2838 }) := by cbv

#print axioms functionIndex41_decoded

theorem functionIndex42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2618, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 2619, limit := 2838 }) := by cbv

#print axioms functionIndex42_decoded

theorem functionIndex43_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2619, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 2620, limit := 2838 }) := by cbv

#print axioms functionIndex43_decoded

theorem functionIndex44_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2620, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 2621, limit := 2838 }) := by cbv

#print axioms functionIndex44_decoded

theorem functionIndex45_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2621, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 2622, limit := 2838 }) := by cbv

#print axioms functionIndex45_decoded

theorem functionIndex46_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2622, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 2623, limit := 2838 }) := by cbv

#print axioms functionIndex46_decoded

theorem functionIndex47_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2623, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 2624, limit := 2838 }) := by cbv

#print axioms functionIndex47_decoded

end Project.EulerCertificate.Artifact
