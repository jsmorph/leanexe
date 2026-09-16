import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart10

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type176_decoded :
    funcType { bytes := artifactBytes, pos := 2207, limit := 2571 } =
      .ok (Cache.raw.types[176]!, { bytes := artifactBytes, pos := 2231, limit := 2571 }) := by cbv

#print axioms type176_decoded

theorem type177_decoded :
    funcType { bytes := artifactBytes, pos := 2231, limit := 2571 } =
      .ok (Cache.raw.types[177]!, { bytes := artifactBytes, pos := 2250, limit := 2571 }) := by cbv

#print axioms type177_decoded

theorem type178_decoded :
    funcType { bytes := artifactBytes, pos := 2250, limit := 2571 } =
      .ok (Cache.raw.types[178]!, { bytes := artifactBytes, pos := 2279, limit := 2571 }) := by cbv

#print axioms type178_decoded

theorem type179_decoded :
    funcType { bytes := artifactBytes, pos := 2279, limit := 2571 } =
      .ok (Cache.raw.types[179]!, { bytes := artifactBytes, pos := 2306, limit := 2571 }) := by cbv

#print axioms type179_decoded

theorem type180_decoded :
    funcType { bytes := artifactBytes, pos := 2306, limit := 2571 } =
      .ok (Cache.raw.types[180]!, { bytes := artifactBytes, pos := 2326, limit := 2571 }) := by cbv

#print axioms type180_decoded

theorem type181_decoded :
    funcType { bytes := artifactBytes, pos := 2326, limit := 2571 } =
      .ok (Cache.raw.types[181]!, { bytes := artifactBytes, pos := 2357, limit := 2571 }) := by cbv

#print axioms type181_decoded

theorem type182_decoded :
    funcType { bytes := artifactBytes, pos := 2357, limit := 2571 } =
      .ok (Cache.raw.types[182]!, { bytes := artifactBytes, pos := 2377, limit := 2571 }) := by cbv

#print axioms type182_decoded

theorem type183_decoded :
    funcType { bytes := artifactBytes, pos := 2377, limit := 2571 } =
      .ok (Cache.raw.types[183]!, { bytes := artifactBytes, pos := 2398, limit := 2571 }) := by cbv

#print axioms type183_decoded

theorem type184_decoded :
    funcType { bytes := artifactBytes, pos := 2398, limit := 2571 } =
      .ok (Cache.raw.types[184]!, { bytes := artifactBytes, pos := 2435, limit := 2571 }) := by cbv

#print axioms type184_decoded

theorem type185_decoded :
    funcType { bytes := artifactBytes, pos := 2435, limit := 2571 } =
      .ok (Cache.raw.types[185]!, { bytes := artifactBytes, pos := 2456, limit := 2571 }) := by cbv

#print axioms type185_decoded

theorem type186_decoded :
    funcType { bytes := artifactBytes, pos := 2456, limit := 2571 } =
      .ok (Cache.raw.types[186]!, { bytes := artifactBytes, pos := 2487, limit := 2571 }) := by cbv

#print axioms type186_decoded

theorem type187_decoded :
    funcType { bytes := artifactBytes, pos := 2487, limit := 2571 } =
      .ok (Cache.raw.types[187]!, { bytes := artifactBytes, pos := 2507, limit := 2571 }) := by cbv

#print axioms type187_decoded

theorem type188_decoded :
    funcType { bytes := artifactBytes, pos := 2507, limit := 2571 } =
      .ok (Cache.raw.types[188]!, { bytes := artifactBytes, pos := 2527, limit := 2571 }) := by cbv

#print axioms type188_decoded

theorem type189_decoded :
    funcType { bytes := artifactBytes, pos := 2527, limit := 2571 } =
      .ok (Cache.raw.types[189]!, { bytes := artifactBytes, pos := 2548, limit := 2571 }) := by cbv

#print axioms type189_decoded

theorem type190_decoded :
    funcType { bytes := artifactBytes, pos := 2548, limit := 2571 } =
      .ok (Cache.raw.types[190]!, { bytes := artifactBytes, pos := 2554, limit := 2571 }) := by cbv

#print axioms type190_decoded

theorem type191_decoded :
    funcType { bytes := artifactBytes, pos := 2554, limit := 2571 } =
      .ok (Cache.raw.types[191]!, { bytes := artifactBytes, pos := 2559, limit := 2571 }) := by cbv

#print axioms type191_decoded

end Project.EulerCertificate.Artifact
