import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionIndex0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2576, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 2577, limit := 2838 }) := by cbv

#print axioms functionIndex0_decoded

theorem functionIndex1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2577, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 2578, limit := 2838 }) := by cbv

#print axioms functionIndex1_decoded

theorem functionIndex2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2578, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 2579, limit := 2838 }) := by cbv

#print axioms functionIndex2_decoded

theorem functionIndex3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2579, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 2580, limit := 2838 }) := by cbv

#print axioms functionIndex3_decoded

theorem functionIndex4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2580, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 2581, limit := 2838 }) := by cbv

#print axioms functionIndex4_decoded

theorem functionIndex5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2581, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 2582, limit := 2838 }) := by cbv

#print axioms functionIndex5_decoded

theorem functionIndex6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2582, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 2583, limit := 2838 }) := by cbv

#print axioms functionIndex6_decoded

theorem functionIndex7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2583, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 2584, limit := 2838 }) := by cbv

#print axioms functionIndex7_decoded

theorem functionIndex8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2584, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 2585, limit := 2838 }) := by cbv

#print axioms functionIndex8_decoded

theorem functionIndex9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2585, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 2586, limit := 2838 }) := by cbv

#print axioms functionIndex9_decoded

theorem functionIndex10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2586, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 2587, limit := 2838 }) := by cbv

#print axioms functionIndex10_decoded

theorem functionIndex11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2587, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 2588, limit := 2838 }) := by cbv

#print axioms functionIndex11_decoded

theorem functionIndex12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2588, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 2589, limit := 2838 }) := by cbv

#print axioms functionIndex12_decoded

theorem functionIndex13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2589, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 2590, limit := 2838 }) := by cbv

#print axioms functionIndex13_decoded

theorem functionIndex14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2590, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 2591, limit := 2838 }) := by cbv

#print axioms functionIndex14_decoded

theorem functionIndex15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 2591, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 2592, limit := 2838 }) := by cbv

#print axioms functionIndex15_decoded

end Project.EulerCertificate.Artifact
