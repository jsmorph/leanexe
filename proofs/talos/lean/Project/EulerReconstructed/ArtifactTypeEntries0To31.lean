import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 13, limit := 1622 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 17, limit := 1622 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 17, limit := 1622 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 23, limit := 1622 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 23, limit := 1622 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 29, limit := 1622 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 29, limit := 1622 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 34, limit := 1622 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 34, limit := 1622 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 43, limit := 1622 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 43, limit := 1622 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 48, limit := 1622 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 48, limit := 1622 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 53, limit := 1622 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 53, limit := 1622 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 58, limit := 1622 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 58, limit := 1622 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 66, limit := 1622 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 66, limit := 1622 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 71, limit := 1622 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 71, limit := 1622 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 76, limit := 1622 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 76, limit := 1622 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 81, limit := 1622 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 81, limit := 1622 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 87, limit := 1622 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 87, limit := 1622 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 92, limit := 1622 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 92, limit := 1622 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 100, limit := 1622 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 100, limit := 1622 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 106, limit := 1622 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 106, limit := 1622 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 112, limit := 1622 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 112, limit := 1622 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 118, limit := 1622 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 118, limit := 1622 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 126, limit := 1622 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 126, limit := 1622 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 132, limit := 1622 }) := by cbv

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 132, limit := 1622 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 138, limit := 1622 }) := by cbv

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 138, limit := 1622 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 146, limit := 1622 }) := by cbv

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 146, limit := 1622 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 154, limit := 1622 }) := by cbv

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 154, limit := 1622 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 162, limit := 1622 }) := by cbv

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 162, limit := 1622 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 167, limit := 1622 }) := by cbv

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 167, limit := 1622 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 172, limit := 1622 }) := by cbv

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 172, limit := 1622 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 178, limit := 1622 }) := by cbv

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 178, limit := 1622 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 185, limit := 1622 }) := by cbv

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 185, limit := 1622 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 193, limit := 1622 }) := by cbv

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 193, limit := 1622 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 201, limit := 1622 }) := by cbv

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 201, limit := 1622 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 209, limit := 1622 }) := by cbv

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 209, limit := 1622 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 217, limit := 1622 }) := by cbv


#print axioms type31_decoded

end Project.EulerReconstructed.Artifact
