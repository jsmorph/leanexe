import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 217, limit := 1622 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 225, limit := 1622 }) := by cbv

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 225, limit := 1622 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 234, limit := 1622 }) := by cbv

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 234, limit := 1622 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 243, limit := 1622 }) := by cbv

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 243, limit := 1622 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 252, limit := 1622 }) := by cbv

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 252, limit := 1622 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 259, limit := 1622 }) := by cbv

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 259, limit := 1622 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 268, limit := 1622 }) := by cbv

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 268, limit := 1622 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 277, limit := 1622 }) := by cbv

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 277, limit := 1622 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 285, limit := 1622 }) := by cbv

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 285, limit := 1622 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 293, limit := 1622 }) := by cbv

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 293, limit := 1622 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 301, limit := 1622 }) := by cbv

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 301, limit := 1622 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 309, limit := 1622 }) := by cbv

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 309, limit := 1622 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 318, limit := 1622 }) := by cbv

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 318, limit := 1622 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 332, limit := 1622 }) := by cbv

theorem type45_decoded :
    funcType { bytes := artifactBytes, pos := 332, limit := 1622 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 346, limit := 1622 }) := by cbv

theorem type46_decoded :
    funcType { bytes := artifactBytes, pos := 346, limit := 1622 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 353, limit := 1622 }) := by cbv

theorem type47_decoded :
    funcType { bytes := artifactBytes, pos := 353, limit := 1622 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 358, limit := 1622 }) := by cbv

theorem type48_decoded :
    funcType { bytes := artifactBytes, pos := 358, limit := 1622 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 363, limit := 1622 }) := by cbv

theorem type49_decoded :
    funcType { bytes := artifactBytes, pos := 363, limit := 1622 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 370, limit := 1622 }) := by cbv

theorem type50_decoded :
    funcType { bytes := artifactBytes, pos := 370, limit := 1622 } =
      .ok (Cache.raw.types[50]!, { bytes := artifactBytes, pos := 376, limit := 1622 }) := by cbv

theorem type51_decoded :
    funcType { bytes := artifactBytes, pos := 376, limit := 1622 } =
      .ok (Cache.raw.types[51]!, { bytes := artifactBytes, pos := 382, limit := 1622 }) := by cbv

theorem type52_decoded :
    funcType { bytes := artifactBytes, pos := 382, limit := 1622 } =
      .ok (Cache.raw.types[52]!, { bytes := artifactBytes, pos := 390, limit := 1622 }) := by cbv

theorem type53_decoded :
    funcType { bytes := artifactBytes, pos := 390, limit := 1622 } =
      .ok (Cache.raw.types[53]!, { bytes := artifactBytes, pos := 398, limit := 1622 }) := by cbv

theorem type54_decoded :
    funcType { bytes := artifactBytes, pos := 398, limit := 1622 } =
      .ok (Cache.raw.types[54]!, { bytes := artifactBytes, pos := 406, limit := 1622 }) := by cbv

theorem type55_decoded :
    funcType { bytes := artifactBytes, pos := 406, limit := 1622 } =
      .ok (Cache.raw.types[55]!, { bytes := artifactBytes, pos := 417, limit := 1622 }) := by cbv

theorem type56_decoded :
    funcType { bytes := artifactBytes, pos := 417, limit := 1622 } =
      .ok (Cache.raw.types[56]!, { bytes := artifactBytes, pos := 429, limit := 1622 }) := by cbv

theorem type57_decoded :
    funcType { bytes := artifactBytes, pos := 429, limit := 1622 } =
      .ok (Cache.raw.types[57]!, { bytes := artifactBytes, pos := 463, limit := 1622 }) := by cbv

theorem type58_decoded :
    funcType { bytes := artifactBytes, pos := 463, limit := 1622 } =
      .ok (Cache.raw.types[58]!, { bytes := artifactBytes, pos := 471, limit := 1622 }) := by cbv

theorem type59_decoded :
    funcType { bytes := artifactBytes, pos := 471, limit := 1622 } =
      .ok (Cache.raw.types[59]!, { bytes := artifactBytes, pos := 486, limit := 1622 }) := by cbv

theorem type60_decoded :
    funcType { bytes := artifactBytes, pos := 486, limit := 1622 } =
      .ok (Cache.raw.types[60]!, { bytes := artifactBytes, pos := 494, limit := 1622 }) := by cbv

theorem type61_decoded :
    funcType { bytes := artifactBytes, pos := 494, limit := 1622 } =
      .ok (Cache.raw.types[61]!, { bytes := artifactBytes, pos := 500, limit := 1622 }) := by cbv

theorem type62_decoded :
    funcType { bytes := artifactBytes, pos := 500, limit := 1622 } =
      .ok (Cache.raw.types[62]!, { bytes := artifactBytes, pos := 515, limit := 1622 }) := by cbv

theorem type63_decoded :
    funcType { bytes := artifactBytes, pos := 515, limit := 1622 } =
      .ok (Cache.raw.types[63]!, { bytes := artifactBytes, pos := 522, limit := 1622 }) := by cbv


#print axioms type63_decoded

end Project.EulerReconstructed.Artifact
