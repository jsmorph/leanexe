import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 107, limit := 364 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 113, limit := 364 }) := by cbv

#print axioms type16_decoded

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 113, limit := 364 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 121, limit := 364 }) := by cbv

#print axioms type17_decoded

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 121, limit := 364 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 127, limit := 364 }) := by cbv

#print axioms type18_decoded

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 127, limit := 364 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 133, limit := 364 }) := by cbv

#print axioms type19_decoded

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 133, limit := 364 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 141, limit := 364 }) := by cbv

#print axioms type20_decoded

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 141, limit := 364 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 149, limit := 364 }) := by cbv

#print axioms type21_decoded

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 149, limit := 364 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 157, limit := 364 }) := by cbv

#print axioms type22_decoded

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 157, limit := 364 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 162, limit := 364 }) := by cbv

#print axioms type23_decoded

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 162, limit := 364 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 167, limit := 364 }) := by cbv

#print axioms type24_decoded

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 167, limit := 364 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 173, limit := 364 }) := by cbv

#print axioms type25_decoded

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 173, limit := 364 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 180, limit := 364 }) := by cbv

#print axioms type26_decoded

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 180, limit := 364 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 188, limit := 364 }) := by cbv

#print axioms type27_decoded

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 188, limit := 364 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 196, limit := 364 }) := by cbv

#print axioms type28_decoded

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 196, limit := 364 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 204, limit := 364 }) := by cbv

#print axioms type29_decoded

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 204, limit := 364 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 212, limit := 364 }) := by cbv

#print axioms type30_decoded

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 212, limit := 364 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 220, limit := 364 }) := by cbv

#print axioms type31_decoded


end Project.EulerOutwardGrid.Artifact
