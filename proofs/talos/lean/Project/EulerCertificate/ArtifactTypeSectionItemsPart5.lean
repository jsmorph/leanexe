import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart4

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type80_decoded :
    funcType { bytes := artifactBytes, pos := 863, limit := 2571 } =
      .ok (Cache.raw.types[80]!, { bytes := artifactBytes, pos := 871, limit := 2571 }) := by cbv

#print axioms type80_decoded

theorem type81_decoded :
    funcType { bytes := artifactBytes, pos := 871, limit := 2571 } =
      .ok (Cache.raw.types[81]!, { bytes := artifactBytes, pos := 880, limit := 2571 }) := by cbv

#print axioms type81_decoded

theorem type82_decoded :
    funcType { bytes := artifactBytes, pos := 880, limit := 2571 } =
      .ok (Cache.raw.types[82]!, { bytes := artifactBytes, pos := 889, limit := 2571 }) := by cbv

#print axioms type82_decoded

theorem type83_decoded :
    funcType { bytes := artifactBytes, pos := 889, limit := 2571 } =
      .ok (Cache.raw.types[83]!, { bytes := artifactBytes, pos := 898, limit := 2571 }) := by cbv

#print axioms type83_decoded

theorem type84_decoded :
    funcType { bytes := artifactBytes, pos := 898, limit := 2571 } =
      .ok (Cache.raw.types[84]!, { bytes := artifactBytes, pos := 905, limit := 2571 }) := by cbv

#print axioms type84_decoded

theorem type85_decoded :
    funcType { bytes := artifactBytes, pos := 905, limit := 2571 } =
      .ok (Cache.raw.types[85]!, { bytes := artifactBytes, pos := 914, limit := 2571 }) := by cbv

#print axioms type85_decoded

theorem type86_decoded :
    funcType { bytes := artifactBytes, pos := 914, limit := 2571 } =
      .ok (Cache.raw.types[86]!, { bytes := artifactBytes, pos := 923, limit := 2571 }) := by cbv

#print axioms type86_decoded

theorem type87_decoded :
    funcType { bytes := artifactBytes, pos := 923, limit := 2571 } =
      .ok (Cache.raw.types[87]!, { bytes := artifactBytes, pos := 932, limit := 2571 }) := by cbv

#print axioms type87_decoded

theorem type88_decoded :
    funcType { bytes := artifactBytes, pos := 932, limit := 2571 } =
      .ok (Cache.raw.types[88]!, { bytes := artifactBytes, pos := 946, limit := 2571 }) := by cbv

#print axioms type88_decoded

theorem type89_decoded :
    funcType { bytes := artifactBytes, pos := 946, limit := 2571 } =
      .ok (Cache.raw.types[89]!, { bytes := artifactBytes, pos := 953, limit := 2571 }) := by cbv

#print axioms type89_decoded

theorem type90_decoded :
    funcType { bytes := artifactBytes, pos := 953, limit := 2571 } =
      .ok (Cache.raw.types[90]!, { bytes := artifactBytes, pos := 958, limit := 2571 }) := by cbv

#print axioms type90_decoded

theorem type91_decoded :
    funcType { bytes := artifactBytes, pos := 958, limit := 2571 } =
      .ok (Cache.raw.types[91]!, { bytes := artifactBytes, pos := 965, limit := 2571 }) := by cbv

#print axioms type91_decoded

theorem type92_decoded :
    funcType { bytes := artifactBytes, pos := 965, limit := 2571 } =
      .ok (Cache.raw.types[92]!, { bytes := artifactBytes, pos := 971, limit := 2571 }) := by cbv

#print axioms type92_decoded

theorem type93_decoded :
    funcType { bytes := artifactBytes, pos := 971, limit := 2571 } =
      .ok (Cache.raw.types[93]!, { bytes := artifactBytes, pos := 977, limit := 2571 }) := by cbv

#print axioms type93_decoded

theorem type94_decoded :
    funcType { bytes := artifactBytes, pos := 977, limit := 2571 } =
      .ok (Cache.raw.types[94]!, { bytes := artifactBytes, pos := 985, limit := 2571 }) := by cbv

#print axioms type94_decoded

theorem type95_decoded :
    funcType { bytes := artifactBytes, pos := 985, limit := 2571 } =
      .ok (Cache.raw.types[95]!, { bytes := artifactBytes, pos := 993, limit := 2571 }) := by cbv

#print axioms type95_decoded

end Project.EulerCertificate.Artifact
