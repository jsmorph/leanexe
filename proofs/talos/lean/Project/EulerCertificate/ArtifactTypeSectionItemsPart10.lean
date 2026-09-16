import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart9

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type160_decoded :
    funcType { bytes := artifactBytes, pos := 1907, limit := 2571 } =
      .ok (Cache.raw.types[160]!, { bytes := artifactBytes, pos := 1918, limit := 2571 }) := by cbv

#print axioms type160_decoded

theorem type161_decoded :
    funcType { bytes := artifactBytes, pos := 1918, limit := 2571 } =
      .ok (Cache.raw.types[161]!, { bytes := artifactBytes, pos := 1924, limit := 2571 }) := by cbv

#print axioms type161_decoded

theorem type162_decoded :
    funcType { bytes := artifactBytes, pos := 1924, limit := 2571 } =
      .ok (Cache.raw.types[162]!, { bytes := artifactBytes, pos := 1937, limit := 2571 }) := by cbv

#print axioms type162_decoded

theorem type163_decoded :
    funcType { bytes := artifactBytes, pos := 1937, limit := 2571 } =
      .ok (Cache.raw.types[163]!, { bytes := artifactBytes, pos := 1965, limit := 2571 }) := by cbv

#print axioms type163_decoded

theorem type164_decoded :
    funcType { bytes := artifactBytes, pos := 1965, limit := 2571 } =
      .ok (Cache.raw.types[164]!, { bytes := artifactBytes, pos := 1975, limit := 2571 }) := by cbv

#print axioms type164_decoded

theorem type165_decoded :
    funcType { bytes := artifactBytes, pos := 1975, limit := 2571 } =
      .ok (Cache.raw.types[165]!, { bytes := artifactBytes, pos := 1987, limit := 2571 }) := by cbv

#print axioms type165_decoded

theorem type166_decoded :
    funcType { bytes := artifactBytes, pos := 1987, limit := 2571 } =
      .ok (Cache.raw.types[166]!, { bytes := artifactBytes, pos := 1997, limit := 2571 }) := by cbv

#print axioms type166_decoded

theorem type167_decoded :
    funcType { bytes := artifactBytes, pos := 1997, limit := 2571 } =
      .ok (Cache.raw.types[167]!, { bytes := artifactBytes, pos := 2016, limit := 2571 }) := by cbv

#print axioms type167_decoded

theorem type168_decoded :
    funcType { bytes := artifactBytes, pos := 2016, limit := 2571 } =
      .ok (Cache.raw.types[168]!, { bytes := artifactBytes, pos := 2031, limit := 2571 }) := by cbv

#print axioms type168_decoded

theorem type169_decoded :
    funcType { bytes := artifactBytes, pos := 2031, limit := 2571 } =
      .ok (Cache.raw.types[169]!, { bytes := artifactBytes, pos := 2055, limit := 2571 }) := by cbv

#print axioms type169_decoded

theorem type170_decoded :
    funcType { bytes := artifactBytes, pos := 2055, limit := 2571 } =
      .ok (Cache.raw.types[170]!, { bytes := artifactBytes, pos := 2077, limit := 2571 }) := by cbv

#print axioms type170_decoded

theorem type171_decoded :
    funcType { bytes := artifactBytes, pos := 2077, limit := 2571 } =
      .ok (Cache.raw.types[171]!, { bytes := artifactBytes, pos := 2116, limit := 2571 }) := by cbv

#print axioms type171_decoded

theorem type172_decoded :
    funcType { bytes := artifactBytes, pos := 2116, limit := 2571 } =
      .ok (Cache.raw.types[172]!, { bytes := artifactBytes, pos := 2137, limit := 2571 }) := by cbv

#print axioms type172_decoded

theorem type173_decoded :
    funcType { bytes := artifactBytes, pos := 2137, limit := 2571 } =
      .ok (Cache.raw.types[173]!, { bytes := artifactBytes, pos := 2157, limit := 2571 }) := by cbv

#print axioms type173_decoded

theorem type174_decoded :
    funcType { bytes := artifactBytes, pos := 2157, limit := 2571 } =
      .ok (Cache.raw.types[174]!, { bytes := artifactBytes, pos := 2185, limit := 2571 }) := by cbv

#print axioms type174_decoded

theorem type175_decoded :
    funcType { bytes := artifactBytes, pos := 2185, limit := 2571 } =
      .ok (Cache.raw.types[175]!, { bytes := artifactBytes, pos := 2207, limit := 2571 }) := by cbv

#print axioms type175_decoded

end Project.EulerCertificate.Artifact
