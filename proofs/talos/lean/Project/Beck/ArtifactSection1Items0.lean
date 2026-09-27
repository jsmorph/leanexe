import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 419 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 22, limit := 419 }) := by cbv

#print axioms type0_decoded

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 22, limit := 419 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 30, limit := 419 }) := by cbv

#print axioms type1_decoded

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 30, limit := 419 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 43, limit := 419 }) := by cbv

#print axioms type2_decoded

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 43, limit := 419 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 51, limit := 419 }) := by cbv

#print axioms type3_decoded

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 51, limit := 419 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 60, limit := 419 }) := by cbv

#print axioms type4_decoded

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 60, limit := 419 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 76, limit := 419 }) := by cbv

#print axioms type5_decoded

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 76, limit := 419 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 87, limit := 419 }) := by cbv

#print axioms type6_decoded

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 419 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 97, limit := 419 }) := by cbv

#print axioms type7_decoded

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 97, limit := 419 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 105, limit := 419 }) := by cbv

#print axioms type8_decoded

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 105, limit := 419 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 110, limit := 419 }) := by cbv

#print axioms type9_decoded

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 110, limit := 419 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 115, limit := 419 }) := by cbv

#print axioms type10_decoded

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 115, limit := 419 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 122, limit := 419 }) := by cbv

#print axioms type11_decoded

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 122, limit := 419 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 130, limit := 419 }) := by cbv

#print axioms type12_decoded

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 130, limit := 419 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 137, limit := 419 }) := by cbv

#print axioms type13_decoded

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 137, limit := 419 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 147, limit := 419 }) := by cbv

#print axioms type14_decoded

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 147, limit := 419 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 157, limit := 419 }) := by cbv

#print axioms type15_decoded


end Project.Beck.Artifact
