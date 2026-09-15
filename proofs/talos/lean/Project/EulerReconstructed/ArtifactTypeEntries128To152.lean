import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type128_decoded :
    funcType { bytes := artifactBytes, pos := 1416, limit := 1622 } =
      .ok (Cache.raw.types[128]!, { bytes := artifactBytes, pos := 1425, limit := 1622 }) := by cbv

theorem type129_decoded :
    funcType { bytes := artifactBytes, pos := 1425, limit := 1622 } =
      .ok (Cache.raw.types[129]!, { bytes := artifactBytes, pos := 1438, limit := 1622 }) := by cbv

theorem type130_decoded :
    funcType { bytes := artifactBytes, pos := 1438, limit := 1622 } =
      .ok (Cache.raw.types[130]!, { bytes := artifactBytes, pos := 1443, limit := 1622 }) := by cbv

theorem type131_decoded :
    funcType { bytes := artifactBytes, pos := 1443, limit := 1622 } =
      .ok (Cache.raw.types[131]!, { bytes := artifactBytes, pos := 1453, limit := 1622 }) := by cbv

theorem type132_decoded :
    funcType { bytes := artifactBytes, pos := 1453, limit := 1622 } =
      .ok (Cache.raw.types[132]!, { bytes := artifactBytes, pos := 1464, limit := 1622 }) := by cbv

theorem type133_decoded :
    funcType { bytes := artifactBytes, pos := 1464, limit := 1622 } =
      .ok (Cache.raw.types[133]!, { bytes := artifactBytes, pos := 1471, limit := 1622 }) := by cbv

theorem type134_decoded :
    funcType { bytes := artifactBytes, pos := 1471, limit := 1622 } =
      .ok (Cache.raw.types[134]!, { bytes := artifactBytes, pos := 1478, limit := 1622 }) := by cbv

theorem type135_decoded :
    funcType { bytes := artifactBytes, pos := 1478, limit := 1622 } =
      .ok (Cache.raw.types[135]!, { bytes := artifactBytes, pos := 1485, limit := 1622 }) := by cbv

theorem type136_decoded :
    funcType { bytes := artifactBytes, pos := 1485, limit := 1622 } =
      .ok (Cache.raw.types[136]!, { bytes := artifactBytes, pos := 1492, limit := 1622 }) := by cbv

theorem type137_decoded :
    funcType { bytes := artifactBytes, pos := 1492, limit := 1622 } =
      .ok (Cache.raw.types[137]!, { bytes := artifactBytes, pos := 1501, limit := 1622 }) := by cbv

theorem type138_decoded :
    funcType { bytes := artifactBytes, pos := 1501, limit := 1622 } =
      .ok (Cache.raw.types[138]!, { bytes := artifactBytes, pos := 1516, limit := 1622 }) := by cbv

theorem type139_decoded :
    funcType { bytes := artifactBytes, pos := 1516, limit := 1622 } =
      .ok (Cache.raw.types[139]!, { bytes := artifactBytes, pos := 1528, limit := 1622 }) := by cbv

theorem type140_decoded :
    funcType { bytes := artifactBytes, pos := 1528, limit := 1622 } =
      .ok (Cache.raw.types[140]!, { bytes := artifactBytes, pos := 1538, limit := 1622 }) := by cbv

theorem type141_decoded :
    funcType { bytes := artifactBytes, pos := 1538, limit := 1622 } =
      .ok (Cache.raw.types[141]!, { bytes := artifactBytes, pos := 1544, limit := 1622 }) := by cbv

theorem type142_decoded :
    funcType { bytes := artifactBytes, pos := 1544, limit := 1622 } =
      .ok (Cache.raw.types[142]!, { bytes := artifactBytes, pos := 1553, limit := 1622 }) := by cbv

theorem type143_decoded :
    funcType { bytes := artifactBytes, pos := 1553, limit := 1622 } =
      .ok (Cache.raw.types[143]!, { bytes := artifactBytes, pos := 1564, limit := 1622 }) := by cbv

theorem type144_decoded :
    funcType { bytes := artifactBytes, pos := 1564, limit := 1622 } =
      .ok (Cache.raw.types[144]!, { bytes := artifactBytes, pos := 1574, limit := 1622 }) := by cbv

theorem type145_decoded :
    funcType { bytes := artifactBytes, pos := 1574, limit := 1622 } =
      .ok (Cache.raw.types[145]!, { bytes := artifactBytes, pos := 1582, limit := 1622 }) := by cbv

theorem type146_decoded :
    funcType { bytes := artifactBytes, pos := 1582, limit := 1622 } =
      .ok (Cache.raw.types[146]!, { bytes := artifactBytes, pos := 1590, limit := 1622 }) := by cbv

theorem type147_decoded :
    funcType { bytes := artifactBytes, pos := 1590, limit := 1622 } =
      .ok (Cache.raw.types[147]!, { bytes := artifactBytes, pos := 1599, limit := 1622 }) := by cbv

theorem type148_decoded :
    funcType { bytes := artifactBytes, pos := 1599, limit := 1622 } =
      .ok (Cache.raw.types[148]!, { bytes := artifactBytes, pos := 1605, limit := 1622 }) := by cbv

theorem type149_decoded :
    funcType { bytes := artifactBytes, pos := 1605, limit := 1622 } =
      .ok (Cache.raw.types[149]!, { bytes := artifactBytes, pos := 1610, limit := 1622 }) := by cbv

theorem type150_decoded :
    funcType { bytes := artifactBytes, pos := 1610, limit := 1622 } =
      .ok (Cache.raw.types[150]!, { bytes := artifactBytes, pos := 1613, limit := 1622 }) := by cbv

theorem type151_decoded :
    funcType { bytes := artifactBytes, pos := 1613, limit := 1622 } =
      .ok (Cache.raw.types[151]!, { bytes := artifactBytes, pos := 1618, limit := 1622 }) := by cbv

theorem type152_decoded :
    funcType { bytes := artifactBytes, pos := 1618, limit := 1622 } =
      .ok (Cache.raw.types[152]!, { bytes := artifactBytes, pos := 1622, limit := 1622 }) := by cbv


#print axioms type152_decoded

end Project.EulerReconstructed.Artifact
