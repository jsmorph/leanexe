import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart3

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type64_decoded :
    funcType { bytes := artifactBytes, pos := 619, limit := 2571 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 627, limit := 2571 }) := by cbv

#print axioms type64_decoded

theorem type65_decoded :
    funcType { bytes := artifactBytes, pos := 627, limit := 2571 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 637, limit := 2571 }) := by cbv

#print axioms type65_decoded

theorem type66_decoded :
    funcType { bytes := artifactBytes, pos := 637, limit := 2571 } =
      .ok (Cache.raw.types[66]!, { bytes := artifactBytes, pos := 665, limit := 2571 }) := by cbv

#print axioms type66_decoded

theorem type67_decoded :
    funcType { bytes := artifactBytes, pos := 665, limit := 2571 } =
      .ok (Cache.raw.types[67]!, { bytes := artifactBytes, pos := 680, limit := 2571 }) := by cbv

#print axioms type67_decoded

theorem type68_decoded :
    funcType { bytes := artifactBytes, pos := 680, limit := 2571 } =
      .ok (Cache.raw.types[68]!, { bytes := artifactBytes, pos := 688, limit := 2571 }) := by cbv

#print axioms type68_decoded

theorem type69_decoded :
    funcType { bytes := artifactBytes, pos := 688, limit := 2571 } =
      .ok (Cache.raw.types[69]!, { bytes := artifactBytes, pos := 700, limit := 2571 }) := by cbv

#print axioms type69_decoded

theorem type70_decoded :
    funcType { bytes := artifactBytes, pos := 700, limit := 2571 } =
      .ok (Cache.raw.types[70]!, { bytes := artifactBytes, pos := 739, limit := 2571 }) := by cbv

#print axioms type70_decoded

theorem type71_decoded :
    funcType { bytes := artifactBytes, pos := 739, limit := 2571 } =
      .ok (Cache.raw.types[71]!, { bytes := artifactBytes, pos := 746, limit := 2571 }) := by cbv

#print axioms type71_decoded

theorem type72_decoded :
    funcType { bytes := artifactBytes, pos := 746, limit := 2571 } =
      .ok (Cache.raw.types[72]!, { bytes := artifactBytes, pos := 765, limit := 2571 }) := by cbv

#print axioms type72_decoded

theorem type73_decoded :
    funcType { bytes := artifactBytes, pos := 765, limit := 2571 } =
      .ok (Cache.raw.types[73]!, { bytes := artifactBytes, pos := 799, limit := 2571 }) := by cbv

#print axioms type73_decoded

theorem type74_decoded :
    funcType { bytes := artifactBytes, pos := 799, limit := 2571 } =
      .ok (Cache.raw.types[74]!, { bytes := artifactBytes, pos := 816, limit := 2571 }) := by cbv

#print axioms type74_decoded

theorem type75_decoded :
    funcType { bytes := artifactBytes, pos := 816, limit := 2571 } =
      .ok (Cache.raw.types[75]!, { bytes := artifactBytes, pos := 834, limit := 2571 }) := by cbv

#print axioms type75_decoded

theorem type76_decoded :
    funcType { bytes := artifactBytes, pos := 834, limit := 2571 } =
      .ok (Cache.raw.types[76]!, { bytes := artifactBytes, pos := 838, limit := 2571 }) := by cbv

#print axioms type76_decoded

theorem type77_decoded :
    funcType { bytes := artifactBytes, pos := 838, limit := 2571 } =
      .ok (Cache.raw.types[77]!, { bytes := artifactBytes, pos := 847, limit := 2571 }) := by cbv

#print axioms type77_decoded

theorem type78_decoded :
    funcType { bytes := artifactBytes, pos := 847, limit := 2571 } =
      .ok (Cache.raw.types[78]!, { bytes := artifactBytes, pos := 855, limit := 2571 }) := by cbv

#print axioms type78_decoded

theorem type79_decoded :
    funcType { bytes := artifactBytes, pos := 855, limit := 2571 } =
      .ok (Cache.raw.types[79]!, { bytes := artifactBytes, pos := 863, limit := 2571 }) := by cbv

#print axioms type79_decoded

end Project.EulerCertificate.Artifact
