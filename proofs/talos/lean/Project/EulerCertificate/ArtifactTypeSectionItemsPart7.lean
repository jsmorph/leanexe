import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart6

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type112_decoded :
    funcType { bytes := artifactBytes, pos := 1200, limit := 2571 } =
      .ok (Cache.raw.types[112]!, { bytes := artifactBytes, pos := 1222, limit := 2571 }) := by cbv

#print axioms type112_decoded

theorem type113_decoded :
    funcType { bytes := artifactBytes, pos := 1222, limit := 2571 } =
      .ok (Cache.raw.types[113]!, { bytes := artifactBytes, pos := 1236, limit := 2571 }) := by cbv

#print axioms type113_decoded

theorem type114_decoded :
    funcType { bytes := artifactBytes, pos := 1236, limit := 2571 } =
      .ok (Cache.raw.types[114]!, { bytes := artifactBytes, pos := 1259, limit := 2571 }) := by cbv

#print axioms type114_decoded

theorem type115_decoded :
    funcType { bytes := artifactBytes, pos := 1259, limit := 2571 } =
      .ok (Cache.raw.types[115]!, { bytes := artifactBytes, pos := 1271, limit := 2571 }) := by cbv

#print axioms type115_decoded

theorem type116_decoded :
    funcType { bytes := artifactBytes, pos := 1271, limit := 2571 } =
      .ok (Cache.raw.types[116]!, { bytes := artifactBytes, pos := 1297, limit := 2571 }) := by cbv

#print axioms type116_decoded

theorem type117_decoded :
    funcType { bytes := artifactBytes, pos := 1297, limit := 2571 } =
      .ok (Cache.raw.types[117]!, { bytes := artifactBytes, pos := 1312, limit := 2571 }) := by cbv

#print axioms type117_decoded

theorem type118_decoded :
    funcType { bytes := artifactBytes, pos := 1312, limit := 2571 } =
      .ok (Cache.raw.types[118]!, { bytes := artifactBytes, pos := 1324, limit := 2571 }) := by cbv

#print axioms type118_decoded

theorem type119_decoded :
    funcType { bytes := artifactBytes, pos := 1324, limit := 2571 } =
      .ok (Cache.raw.types[119]!, { bytes := artifactBytes, pos := 1329, limit := 2571 }) := by cbv

#print axioms type119_decoded

theorem type120_decoded :
    funcType { bytes := artifactBytes, pos := 1329, limit := 2571 } =
      .ok (Cache.raw.types[120]!, { bytes := artifactBytes, pos := 1334, limit := 2571 }) := by cbv

#print axioms type120_decoded

theorem type121_decoded :
    funcType { bytes := artifactBytes, pos := 1334, limit := 2571 } =
      .ok (Cache.raw.types[121]!, { bytes := artifactBytes, pos := 1339, limit := 2571 }) := by cbv

#print axioms type121_decoded

theorem type122_decoded :
    funcType { bytes := artifactBytes, pos := 1339, limit := 2571 } =
      .ok (Cache.raw.types[122]!, { bytes := artifactBytes, pos := 1344, limit := 2571 }) := by cbv

#print axioms type122_decoded

theorem type123_decoded :
    funcType { bytes := artifactBytes, pos := 1344, limit := 2571 } =
      .ok (Cache.raw.types[123]!, { bytes := artifactBytes, pos := 1354, limit := 2571 }) := by cbv

#print axioms type123_decoded

theorem type124_decoded :
    funcType { bytes := artifactBytes, pos := 1354, limit := 2571 } =
      .ok (Cache.raw.types[124]!, { bytes := artifactBytes, pos := 1364, limit := 2571 }) := by cbv

#print axioms type124_decoded

theorem type125_decoded :
    funcType { bytes := artifactBytes, pos := 1364, limit := 2571 } =
      .ok (Cache.raw.types[125]!, { bytes := artifactBytes, pos := 1376, limit := 2571 }) := by cbv

#print axioms type125_decoded

theorem type126_decoded :
    funcType { bytes := artifactBytes, pos := 1376, limit := 2571 } =
      .ok (Cache.raw.types[126]!, { bytes := artifactBytes, pos := 1388, limit := 2571 }) := by cbv

#print axioms type126_decoded

theorem type127_decoded :
    funcType { bytes := artifactBytes, pos := 1388, limit := 2571 } =
      .ok (Cache.raw.types[127]!, { bytes := artifactBytes, pos := 1400, limit := 2571 }) := by cbv

#print axioms type127_decoded

end Project.EulerCertificate.Artifact
