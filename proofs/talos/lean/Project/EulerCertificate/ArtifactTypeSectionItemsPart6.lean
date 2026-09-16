import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart5

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type96_decoded :
    funcType { bytes := artifactBytes, pos := 993, limit := 2571 } =
      .ok (Cache.raw.types[96]!, { bytes := artifactBytes, pos := 1001, limit := 2571 }) := by cbv

#print axioms type96_decoded

theorem type97_decoded :
    funcType { bytes := artifactBytes, pos := 1001, limit := 2571 } =
      .ok (Cache.raw.types[97]!, { bytes := artifactBytes, pos := 1013, limit := 2571 }) := by cbv

#print axioms type97_decoded

theorem type98_decoded :
    funcType { bytes := artifactBytes, pos := 1013, limit := 2571 } =
      .ok (Cache.raw.types[98]!, { bytes := artifactBytes, pos := 1047, limit := 2571 }) := by cbv

#print axioms type98_decoded

theorem type99_decoded :
    funcType { bytes := artifactBytes, pos := 1047, limit := 2571 } =
      .ok (Cache.raw.types[99]!, { bytes := artifactBytes, pos := 1055, limit := 2571 }) := by cbv

#print axioms type99_decoded

theorem type100_decoded :
    funcType { bytes := artifactBytes, pos := 1055, limit := 2571 } =
      .ok (Cache.raw.types[100]!, { bytes := artifactBytes, pos := 1070, limit := 2571 }) := by cbv

#print axioms type100_decoded

theorem type101_decoded :
    funcType { bytes := artifactBytes, pos := 1070, limit := 2571 } =
      .ok (Cache.raw.types[101]!, { bytes := artifactBytes, pos := 1078, limit := 2571 }) := by cbv

#print axioms type101_decoded

theorem type102_decoded :
    funcType { bytes := artifactBytes, pos := 1078, limit := 2571 } =
      .ok (Cache.raw.types[102]!, { bytes := artifactBytes, pos := 1084, limit := 2571 }) := by cbv

#print axioms type102_decoded

theorem type103_decoded :
    funcType { bytes := artifactBytes, pos := 1084, limit := 2571 } =
      .ok (Cache.raw.types[103]!, { bytes := artifactBytes, pos := 1099, limit := 2571 }) := by cbv

#print axioms type103_decoded

theorem type104_decoded :
    funcType { bytes := artifactBytes, pos := 1099, limit := 2571 } =
      .ok (Cache.raw.types[104]!, { bytes := artifactBytes, pos := 1106, limit := 2571 }) := by cbv

#print axioms type104_decoded

theorem type105_decoded :
    funcType { bytes := artifactBytes, pos := 1106, limit := 2571 } =
      .ok (Cache.raw.types[105]!, { bytes := artifactBytes, pos := 1114, limit := 2571 }) := by cbv

#print axioms type105_decoded

theorem type106_decoded :
    funcType { bytes := artifactBytes, pos := 1114, limit := 2571 } =
      .ok (Cache.raw.types[106]!, { bytes := artifactBytes, pos := 1134, limit := 2571 }) := by cbv

#print axioms type106_decoded

theorem type107_decoded :
    funcType { bytes := artifactBytes, pos := 1134, limit := 2571 } =
      .ok (Cache.raw.types[107]!, { bytes := artifactBytes, pos := 1143, limit := 2571 }) := by cbv

#print axioms type107_decoded

theorem type108_decoded :
    funcType { bytes := artifactBytes, pos := 1143, limit := 2571 } =
      .ok (Cache.raw.types[108]!, { bytes := artifactBytes, pos := 1160, limit := 2571 }) := by cbv

#print axioms type108_decoded

theorem type109_decoded :
    funcType { bytes := artifactBytes, pos := 1160, limit := 2571 } =
      .ok (Cache.raw.types[109]!, { bytes := artifactBytes, pos := 1172, limit := 2571 }) := by cbv

#print axioms type109_decoded

theorem type110_decoded :
    funcType { bytes := artifactBytes, pos := 1172, limit := 2571 } =
      .ok (Cache.raw.types[110]!, { bytes := artifactBytes, pos := 1187, limit := 2571 }) := by cbv

#print axioms type110_decoded

theorem type111_decoded :
    funcType { bytes := artifactBytes, pos := 1187, limit := 2571 } =
      .ok (Cache.raw.types[111]!, { bytes := artifactBytes, pos := 1200, limit := 2571 }) := by cbv

#print axioms type111_decoded

end Project.EulerCertificate.Artifact
