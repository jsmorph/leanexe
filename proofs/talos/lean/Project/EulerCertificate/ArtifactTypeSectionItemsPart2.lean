import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactTypeSectionItemsPart1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 378, limit := 2571 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 383, limit := 2571 }) := by cbv

#print axioms type32_decoded

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 383, limit := 2571 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 388, limit := 2571 }) := by cbv

#print axioms type33_decoded

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 388, limit := 2571 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 394, limit := 2571 }) := by cbv

#print axioms type34_decoded

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 394, limit := 2571 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 399, limit := 2571 }) := by cbv

#print axioms type35_decoded

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 399, limit := 2571 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 407, limit := 2571 }) := by cbv

#print axioms type36_decoded

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 407, limit := 2571 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 413, limit := 2571 }) := by cbv

#print axioms type37_decoded

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 413, limit := 2571 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 419, limit := 2571 }) := by cbv

#print axioms type38_decoded

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 419, limit := 2571 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 425, limit := 2571 }) := by cbv

#print axioms type39_decoded

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 425, limit := 2571 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 433, limit := 2571 }) := by cbv

#print axioms type40_decoded

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 433, limit := 2571 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 439, limit := 2571 }) := by cbv

#print axioms type41_decoded

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 439, limit := 2571 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 445, limit := 2571 }) := by cbv

#print axioms type42_decoded

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 445, limit := 2571 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 453, limit := 2571 }) := by cbv

#print axioms type43_decoded

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 453, limit := 2571 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 461, limit := 2571 }) := by cbv

#print axioms type44_decoded

theorem type45_decoded :
    funcType { bytes := artifactBytes, pos := 461, limit := 2571 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 469, limit := 2571 }) := by cbv

#print axioms type45_decoded

theorem type46_decoded :
    funcType { bytes := artifactBytes, pos := 469, limit := 2571 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 480, limit := 2571 }) := by cbv

#print axioms type46_decoded

theorem type47_decoded :
    funcType { bytes := artifactBytes, pos := 480, limit := 2571 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 495, limit := 2571 }) := by cbv

#print axioms type47_decoded

end Project.EulerCertificate.Artifact
