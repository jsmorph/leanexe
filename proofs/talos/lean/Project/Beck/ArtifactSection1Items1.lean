import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 157, limit := 419 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 168, limit := 419 }) := by cbv

#print axioms type16_decoded

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 168, limit := 419 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 182, limit := 419 }) := by cbv

#print axioms type17_decoded

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 182, limit := 419 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 192, limit := 419 }) := by cbv

#print axioms type18_decoded

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 192, limit := 419 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 206, limit := 419 }) := by cbv

#print axioms type19_decoded

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 206, limit := 419 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 213, limit := 419 }) := by cbv

#print axioms type20_decoded

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 213, limit := 419 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 223, limit := 419 }) := by cbv

#print axioms type21_decoded

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 223, limit := 419 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 233, limit := 419 }) := by cbv

#print axioms type22_decoded

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 233, limit := 419 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 241, limit := 419 }) := by cbv

#print axioms type23_decoded

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 241, limit := 419 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 253, limit := 419 }) := by cbv

#print axioms type24_decoded

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 253, limit := 419 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 272, limit := 419 }) := by cbv

#print axioms type25_decoded

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 272, limit := 419 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 288, limit := 419 }) := by cbv

#print axioms type26_decoded

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 288, limit := 419 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 305, limit := 419 }) := by cbv

#print axioms type27_decoded

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 305, limit := 419 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 320, limit := 419 }) := by cbv

#print axioms type28_decoded

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 320, limit := 419 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 329, limit := 419 }) := by cbv

#print axioms type29_decoded

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 329, limit := 419 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 343, limit := 419 }) := by cbv

#print axioms type30_decoded

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 343, limit := 419 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 350, limit := 419 }) := by cbv

#print axioms type31_decoded


end Project.Beck.Artifact
