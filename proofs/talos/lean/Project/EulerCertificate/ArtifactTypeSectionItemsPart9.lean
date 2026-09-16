import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart8

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type144_decoded :
    funcType { bytes := artifactBytes, pos := 1599, limit := 2571 } =
      .ok (Cache.raw.types[144]!, { bytes := artifactBytes, pos := 1616, limit := 2571 }) := by cbv

#print axioms type144_decoded

theorem type145_decoded :
    funcType { bytes := artifactBytes, pos := 1616, limit := 2571 } =
      .ok (Cache.raw.types[145]!, { bytes := artifactBytes, pos := 1633, limit := 2571 }) := by cbv

#print axioms type145_decoded

theorem type146_decoded :
    funcType { bytes := artifactBytes, pos := 1633, limit := 2571 } =
      .ok (Cache.raw.types[146]!, { bytes := artifactBytes, pos := 1666, limit := 2571 }) := by cbv

#print axioms type146_decoded

theorem type147_decoded :
    funcType { bytes := artifactBytes, pos := 1666, limit := 2571 } =
      .ok (Cache.raw.types[147]!, { bytes := artifactBytes, pos := 1693, limit := 2571 }) := by cbv

#print axioms type147_decoded

theorem type148_decoded :
    funcType { bytes := artifactBytes, pos := 1693, limit := 2571 } =
      .ok (Cache.raw.types[148]!, { bytes := artifactBytes, pos := 1720, limit := 2571 }) := by cbv

#print axioms type148_decoded

theorem type149_decoded :
    funcType { bytes := artifactBytes, pos := 1720, limit := 2571 } =
      .ok (Cache.raw.types[149]!, { bytes := artifactBytes, pos := 1747, limit := 2571 }) := by cbv

#print axioms type149_decoded

theorem type150_decoded :
    funcType { bytes := artifactBytes, pos := 1747, limit := 2571 } =
      .ok (Cache.raw.types[150]!, { bytes := artifactBytes, pos := 1774, limit := 2571 }) := by cbv

#print axioms type150_decoded

theorem type151_decoded :
    funcType { bytes := artifactBytes, pos := 1774, limit := 2571 } =
      .ok (Cache.raw.types[151]!, { bytes := artifactBytes, pos := 1801, limit := 2571 }) := by cbv

#print axioms type151_decoded

theorem type152_decoded :
    funcType { bytes := artifactBytes, pos := 1801, limit := 2571 } =
      .ok (Cache.raw.types[152]!, { bytes := artifactBytes, pos := 1813, limit := 2571 }) := by cbv

#print axioms type152_decoded

theorem type153_decoded :
    funcType { bytes := artifactBytes, pos := 1813, limit := 2571 } =
      .ok (Cache.raw.types[153]!, { bytes := artifactBytes, pos := 1825, limit := 2571 }) := by cbv

#print axioms type153_decoded

theorem type154_decoded :
    funcType { bytes := artifactBytes, pos := 1825, limit := 2571 } =
      .ok (Cache.raw.types[154]!, { bytes := artifactBytes, pos := 1837, limit := 2571 }) := by cbv

#print axioms type154_decoded

theorem type155_decoded :
    funcType { bytes := artifactBytes, pos := 1837, limit := 2571 } =
      .ok (Cache.raw.types[155]!, { bytes := artifactBytes, pos := 1849, limit := 2571 }) := by cbv

#print axioms type155_decoded

theorem type156_decoded :
    funcType { bytes := artifactBytes, pos := 1849, limit := 2571 } =
      .ok (Cache.raw.types[156]!, { bytes := artifactBytes, pos := 1861, limit := 2571 }) := by cbv

#print axioms type156_decoded

theorem type157_decoded :
    funcType { bytes := artifactBytes, pos := 1861, limit := 2571 } =
      .ok (Cache.raw.types[157]!, { bytes := artifactBytes, pos := 1873, limit := 2571 }) := by cbv

#print axioms type157_decoded

theorem type158_decoded :
    funcType { bytes := artifactBytes, pos := 1873, limit := 2571 } =
      .ok (Cache.raw.types[158]!, { bytes := artifactBytes, pos := 1896, limit := 2571 }) := by cbv

#print axioms type158_decoded

theorem type159_decoded :
    funcType { bytes := artifactBytes, pos := 1896, limit := 2571 } =
      .ok (Cache.raw.types[159]!, { bytes := artifactBytes, pos := 1907, limit := 2571 }) := by cbv

#print axioms type159_decoded

end Project.EulerCertificate.Artifact
