import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart7

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type128_decoded :
    funcType { bytes := artifactBytes, pos := 1400, limit := 2571 } =
      .ok (Cache.raw.types[128]!, { bytes := artifactBytes, pos := 1412, limit := 2571 }) := by cbv

#print axioms type128_decoded

theorem type129_decoded :
    funcType { bytes := artifactBytes, pos := 1412, limit := 2571 } =
      .ok (Cache.raw.types[129]!, { bytes := artifactBytes, pos := 1418, limit := 2571 }) := by cbv

#print axioms type129_decoded

theorem type130_decoded :
    funcType { bytes := artifactBytes, pos := 1418, limit := 2571 } =
      .ok (Cache.raw.types[130]!, { bytes := artifactBytes, pos := 1424, limit := 2571 }) := by cbv

#print axioms type130_decoded

theorem type131_decoded :
    funcType { bytes := artifactBytes, pos := 1424, limit := 2571 } =
      .ok (Cache.raw.types[131]!, { bytes := artifactBytes, pos := 1433, limit := 2571 }) := by cbv

#print axioms type131_decoded

theorem type132_decoded :
    funcType { bytes := artifactBytes, pos := 1433, limit := 2571 } =
      .ok (Cache.raw.types[132]!, { bytes := artifactBytes, pos := 1450, limit := 2571 }) := by cbv

#print axioms type132_decoded

theorem type133_decoded :
    funcType { bytes := artifactBytes, pos := 1450, limit := 2571 } =
      .ok (Cache.raw.types[133]!, { bytes := artifactBytes, pos := 1460, limit := 2571 }) := by cbv

#print axioms type133_decoded

theorem type134_decoded :
    funcType { bytes := artifactBytes, pos := 1460, limit := 2571 } =
      .ok (Cache.raw.types[134]!, { bytes := artifactBytes, pos := 1470, limit := 2571 }) := by cbv

#print axioms type134_decoded

theorem type135_decoded :
    funcType { bytes := artifactBytes, pos := 1470, limit := 2571 } =
      .ok (Cache.raw.types[135]!, { bytes := artifactBytes, pos := 1479, limit := 2571 }) := by cbv

#print axioms type135_decoded

theorem type136_decoded :
    funcType { bytes := artifactBytes, pos := 1479, limit := 2571 } =
      .ok (Cache.raw.types[136]!, { bytes := artifactBytes, pos := 1488, limit := 2571 }) := by cbv

#print axioms type136_decoded

theorem type137_decoded :
    funcType { bytes := artifactBytes, pos := 1488, limit := 2571 } =
      .ok (Cache.raw.types[137]!, { bytes := artifactBytes, pos := 1498, limit := 2571 }) := by cbv

#print axioms type137_decoded

theorem type138_decoded :
    funcType { bytes := artifactBytes, pos := 1498, limit := 2571 } =
      .ok (Cache.raw.types[138]!, { bytes := artifactBytes, pos := 1508, limit := 2571 }) := by cbv

#print axioms type138_decoded

theorem type139_decoded :
    funcType { bytes := artifactBytes, pos := 1508, limit := 2571 } =
      .ok (Cache.raw.types[139]!, { bytes := artifactBytes, pos := 1518, limit := 2571 }) := by cbv

#print axioms type139_decoded

theorem type140_decoded :
    funcType { bytes := artifactBytes, pos := 1518, limit := 2571 } =
      .ok (Cache.raw.types[140]!, { bytes := artifactBytes, pos := 1528, limit := 2571 }) := by cbv

#print axioms type140_decoded

theorem type141_decoded :
    funcType { bytes := artifactBytes, pos := 1528, limit := 2571 } =
      .ok (Cache.raw.types[141]!, { bytes := artifactBytes, pos := 1539, limit := 2571 }) := by cbv

#print axioms type141_decoded

theorem type142_decoded :
    funcType { bytes := artifactBytes, pos := 1539, limit := 2571 } =
      .ok (Cache.raw.types[142]!, { bytes := artifactBytes, pos := 1567, limit := 2571 }) := by cbv

#print axioms type142_decoded

theorem type143_decoded :
    funcType { bytes := artifactBytes, pos := 1567, limit := 2571 } =
      .ok (Cache.raw.types[143]!, { bytes := artifactBytes, pos := 1599, limit := 2571 }) := by cbv

#print axioms type143_decoded

end Project.EulerCertificate.Artifact
