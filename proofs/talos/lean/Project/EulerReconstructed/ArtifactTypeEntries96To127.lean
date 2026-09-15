import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type96_decoded :
    funcType { bytes := artifactBytes, pos := 909, limit := 1622 } =
      .ok (Cache.raw.types[96]!, { bytes := artifactBytes, pos := 918, limit := 1622 }) := by cbv

theorem type97_decoded :
    funcType { bytes := artifactBytes, pos := 918, limit := 1622 } =
      .ok (Cache.raw.types[97]!, { bytes := artifactBytes, pos := 927, limit := 1622 }) := by cbv

theorem type98_decoded :
    funcType { bytes := artifactBytes, pos := 927, limit := 1622 } =
      .ok (Cache.raw.types[98]!, { bytes := artifactBytes, pos := 937, limit := 1622 }) := by cbv

theorem type99_decoded :
    funcType { bytes := artifactBytes, pos := 937, limit := 1622 } =
      .ok (Cache.raw.types[99]!, { bytes := artifactBytes, pos := 947, limit := 1622 }) := by cbv

theorem type100_decoded :
    funcType { bytes := artifactBytes, pos := 947, limit := 1622 } =
      .ok (Cache.raw.types[100]!, { bytes := artifactBytes, pos := 957, limit := 1622 }) := by cbv

theorem type101_decoded :
    funcType { bytes := artifactBytes, pos := 957, limit := 1622 } =
      .ok (Cache.raw.types[101]!, { bytes := artifactBytes, pos := 967, limit := 1622 }) := by cbv

theorem type102_decoded :
    funcType { bytes := artifactBytes, pos := 967, limit := 1622 } =
      .ok (Cache.raw.types[102]!, { bytes := artifactBytes, pos := 979, limit := 1622 }) := by cbv

theorem type103_decoded :
    funcType { bytes := artifactBytes, pos := 979, limit := 1622 } =
      .ok (Cache.raw.types[103]!, { bytes := artifactBytes, pos := 990, limit := 1622 }) := by cbv

theorem type104_decoded :
    funcType { bytes := artifactBytes, pos := 990, limit := 1622 } =
      .ok (Cache.raw.types[104]!, { bytes := artifactBytes, pos := 1018, limit := 1622 }) := by cbv

theorem type105_decoded :
    funcType { bytes := artifactBytes, pos := 1018, limit := 1622 } =
      .ok (Cache.raw.types[105]!, { bytes := artifactBytes, pos := 1050, limit := 1622 }) := by cbv

theorem type106_decoded :
    funcType { bytes := artifactBytes, pos := 1050, limit := 1622 } =
      .ok (Cache.raw.types[106]!, { bytes := artifactBytes, pos := 1067, limit := 1622 }) := by cbv

theorem type107_decoded :
    funcType { bytes := artifactBytes, pos := 1067, limit := 1622 } =
      .ok (Cache.raw.types[107]!, { bytes := artifactBytes, pos := 1084, limit := 1622 }) := by cbv

theorem type108_decoded :
    funcType { bytes := artifactBytes, pos := 1084, limit := 1622 } =
      .ok (Cache.raw.types[108]!, { bytes := artifactBytes, pos := 1117, limit := 1622 }) := by cbv

theorem type109_decoded :
    funcType { bytes := artifactBytes, pos := 1117, limit := 1622 } =
      .ok (Cache.raw.types[109]!, { bytes := artifactBytes, pos := 1144, limit := 1622 }) := by cbv

theorem type110_decoded :
    funcType { bytes := artifactBytes, pos := 1144, limit := 1622 } =
      .ok (Cache.raw.types[110]!, { bytes := artifactBytes, pos := 1171, limit := 1622 }) := by cbv

theorem type111_decoded :
    funcType { bytes := artifactBytes, pos := 1171, limit := 1622 } =
      .ok (Cache.raw.types[111]!, { bytes := artifactBytes, pos := 1198, limit := 1622 }) := by cbv

theorem type112_decoded :
    funcType { bytes := artifactBytes, pos := 1198, limit := 1622 } =
      .ok (Cache.raw.types[112]!, { bytes := artifactBytes, pos := 1225, limit := 1622 }) := by cbv

theorem type113_decoded :
    funcType { bytes := artifactBytes, pos := 1225, limit := 1622 } =
      .ok (Cache.raw.types[113]!, { bytes := artifactBytes, pos := 1252, limit := 1622 }) := by cbv

theorem type114_decoded :
    funcType { bytes := artifactBytes, pos := 1252, limit := 1622 } =
      .ok (Cache.raw.types[114]!, { bytes := artifactBytes, pos := 1264, limit := 1622 }) := by cbv

theorem type115_decoded :
    funcType { bytes := artifactBytes, pos := 1264, limit := 1622 } =
      .ok (Cache.raw.types[115]!, { bytes := artifactBytes, pos := 1276, limit := 1622 }) := by cbv

theorem type116_decoded :
    funcType { bytes := artifactBytes, pos := 1276, limit := 1622 } =
      .ok (Cache.raw.types[116]!, { bytes := artifactBytes, pos := 1288, limit := 1622 }) := by cbv

theorem type117_decoded :
    funcType { bytes := artifactBytes, pos := 1288, limit := 1622 } =
      .ok (Cache.raw.types[117]!, { bytes := artifactBytes, pos := 1300, limit := 1622 }) := by cbv

theorem type118_decoded :
    funcType { bytes := artifactBytes, pos := 1300, limit := 1622 } =
      .ok (Cache.raw.types[118]!, { bytes := artifactBytes, pos := 1312, limit := 1622 }) := by cbv

theorem type119_decoded :
    funcType { bytes := artifactBytes, pos := 1312, limit := 1622 } =
      .ok (Cache.raw.types[119]!, { bytes := artifactBytes, pos := 1324, limit := 1622 }) := by cbv

theorem type120_decoded :
    funcType { bytes := artifactBytes, pos := 1324, limit := 1622 } =
      .ok (Cache.raw.types[120]!, { bytes := artifactBytes, pos := 1347, limit := 1622 }) := by cbv

theorem type121_decoded :
    funcType { bytes := artifactBytes, pos := 1347, limit := 1622 } =
      .ok (Cache.raw.types[121]!, { bytes := artifactBytes, pos := 1358, limit := 1622 }) := by cbv

theorem type122_decoded :
    funcType { bytes := artifactBytes, pos := 1358, limit := 1622 } =
      .ok (Cache.raw.types[122]!, { bytes := artifactBytes, pos := 1369, limit := 1622 }) := by cbv

theorem type123_decoded :
    funcType { bytes := artifactBytes, pos := 1369, limit := 1622 } =
      .ok (Cache.raw.types[123]!, { bytes := artifactBytes, pos := 1375, limit := 1622 }) := by cbv

theorem type124_decoded :
    funcType { bytes := artifactBytes, pos := 1375, limit := 1622 } =
      .ok (Cache.raw.types[124]!, { bytes := artifactBytes, pos := 1385, limit := 1622 }) := by cbv

theorem type125_decoded :
    funcType { bytes := artifactBytes, pos := 1385, limit := 1622 } =
      .ok (Cache.raw.types[125]!, { bytes := artifactBytes, pos := 1400, limit := 1622 }) := by cbv

theorem type126_decoded :
    funcType { bytes := artifactBytes, pos := 1400, limit := 1622 } =
      .ok (Cache.raw.types[126]!, { bytes := artifactBytes, pos := 1408, limit := 1622 }) := by cbv

theorem type127_decoded :
    funcType { bytes := artifactBytes, pos := 1408, limit := 1622 } =
      .ok (Cache.raw.types[127]!, { bytes := artifactBytes, pos := 1416, limit := 1622 }) := by cbv


#print axioms type127_decoded

end Project.EulerReconstructed.Artifact
