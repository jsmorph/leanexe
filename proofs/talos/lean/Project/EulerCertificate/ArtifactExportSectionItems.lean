import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem export0_decoded :
    exportEntry { bytes := artifactBytes, pos := 2880, limit := 2999 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 2889, limit := 2999 }) := by cbv

#print axioms export0_decoded

theorem export1_decoded :
    exportEntry { bytes := artifactBytes, pos := 2889, limit := 2999 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 2898, limit := 2999 }) := by cbv

#print axioms export1_decoded

theorem export2_decoded :
    exportEntry { bytes := artifactBytes, pos := 2898, limit := 2999 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 2907, limit := 2999 }) := by cbv

#print axioms export2_decoded

theorem export3_decoded :
    exportEntry { bytes := artifactBytes, pos := 2907, limit := 2999 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 2916, limit := 2999 }) := by cbv

#print axioms export3_decoded

theorem export4_decoded :
    exportEntry { bytes := artifactBytes, pos := 2916, limit := 2999 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 2926, limit := 2999 }) := by cbv

#print axioms export4_decoded

theorem export5_decoded :
    exportEntry { bytes := artifactBytes, pos := 2926, limit := 2999 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 2937, limit := 2999 }) := by cbv

#print axioms export5_decoded

theorem export6_decoded :
    exportEntry { bytes := artifactBytes, pos := 2937, limit := 2999 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 2945, limit := 2999 }) := by cbv

#print axioms export6_decoded

theorem export7_decoded :
    exportEntry { bytes := artifactBytes, pos := 2945, limit := 2999 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 2958, limit := 2999 }) := by cbv

#print axioms export7_decoded

theorem export8_decoded :
    exportEntry { bytes := artifactBytes, pos := 2958, limit := 2999 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 2972, limit := 2999 }) := by cbv

#print axioms export8_decoded

theorem export9_decoded :
    exportEntry { bytes := artifactBytes, pos := 2972, limit := 2999 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 2987, limit := 2999 }) := by cbv

#print axioms export9_decoded

theorem export10_decoded :
    exportEntry { bytes := artifactBytes, pos := 2987, limit := 2999 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 2999, limit := 2999 }) := by cbv

#print axioms export10_decoded

end Project.EulerCertificate.Artifact
