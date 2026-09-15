import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem export0_decoded :
    exportEntry { bytes := artifactBytes, pos := 770, limit := 897 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 779, limit := 897 }) := by cbv

theorem export1_decoded :
    exportEntry { bytes := artifactBytes, pos := 779, limit := 897 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 801, limit := 897 }) := by cbv

theorem export2_decoded :
    exportEntry { bytes := artifactBytes, pos := 801, limit := 897 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 809, limit := 897 }) := by cbv

theorem export3_decoded :
    exportEntry { bytes := artifactBytes, pos := 809, limit := 897 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 817, limit := 897 }) := by cbv

theorem export4_decoded :
    exportEntry { bytes := artifactBytes, pos := 817, limit := 897 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 826, limit := 897 }) := by cbv

theorem export5_decoded :
    exportEntry { bytes := artifactBytes, pos := 826, limit := 897 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 836, limit := 897 }) := by cbv

theorem export6_decoded :
    exportEntry { bytes := artifactBytes, pos := 836, limit := 897 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 843, limit := 897 }) := by cbv

theorem export7_decoded :
    exportEntry { bytes := artifactBytes, pos := 843, limit := 897 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 856, limit := 897 }) := by cbv

theorem export8_decoded :
    exportEntry { bytes := artifactBytes, pos := 856, limit := 897 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 870, limit := 897 }) := by cbv

theorem export9_decoded :
    exportEntry { bytes := artifactBytes, pos := 870, limit := 897 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 885, limit := 897 }) := by cbv

theorem export10_decoded :
    exportEntry { bytes := artifactBytes, pos := 885, limit := 897 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 897, limit := 897 }) := by cbv

theorem exports_tail11_decoded :
    Internal.vectorLoop exportEntry 0 { bytes := artifactBytes, pos := 897, limit := 897 } =
      .ok (Cache.raw.exports.drop 11, { bytes := artifactBytes, pos := 897, limit := 897 }) := by rfl

theorem exports_tail10_decoded :
    Internal.vectorLoop exportEntry 1 { bytes := artifactBytes, pos := 885, limit := 897 } =
      .ok (Cache.raw.exports.drop 10, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export10_decoded exports_tail11_decoded

theorem exports_tail9_decoded :
    Internal.vectorLoop exportEntry 2 { bytes := artifactBytes, pos := 870, limit := 897 } =
      .ok (Cache.raw.exports.drop 9, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export9_decoded exports_tail10_decoded

theorem exports_tail8_decoded :
    Internal.vectorLoop exportEntry 3 { bytes := artifactBytes, pos := 856, limit := 897 } =
      .ok (Cache.raw.exports.drop 8, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export8_decoded exports_tail9_decoded

theorem exports_tail7_decoded :
    Internal.vectorLoop exportEntry 4 { bytes := artifactBytes, pos := 843, limit := 897 } =
      .ok (Cache.raw.exports.drop 7, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export7_decoded exports_tail8_decoded

theorem exports_tail6_decoded :
    Internal.vectorLoop exportEntry 5 { bytes := artifactBytes, pos := 836, limit := 897 } =
      .ok (Cache.raw.exports.drop 6, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export6_decoded exports_tail7_decoded

theorem exports_tail5_decoded :
    Internal.vectorLoop exportEntry 6 { bytes := artifactBytes, pos := 826, limit := 897 } =
      .ok (Cache.raw.exports.drop 5, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export5_decoded exports_tail6_decoded

theorem exports_tail4_decoded :
    Internal.vectorLoop exportEntry 7 { bytes := artifactBytes, pos := 817, limit := 897 } =
      .ok (Cache.raw.exports.drop 4, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export4_decoded exports_tail5_decoded

theorem exports_tail3_decoded :
    Internal.vectorLoop exportEntry 8 { bytes := artifactBytes, pos := 809, limit := 897 } =
      .ok (Cache.raw.exports.drop 3, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export3_decoded exports_tail4_decoded

theorem exports_tail2_decoded :
    Internal.vectorLoop exportEntry 9 { bytes := artifactBytes, pos := 801, limit := 897 } =
      .ok (Cache.raw.exports.drop 2, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export2_decoded exports_tail3_decoded

theorem exports_tail1_decoded :
    Internal.vectorLoop exportEntry 10 { bytes := artifactBytes, pos := 779, limit := 897 } =
      .ok (Cache.raw.exports.drop 1, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export1_decoded exports_tail2_decoded

theorem exports_tail0_decoded :
    Internal.vectorLoop exportEntry 11 { bytes := artifactBytes, pos := 770, limit := 897 } =
      .ok (Cache.raw.exports.drop 0, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  exact vectorLoop_eq_cons export0_decoded exports_tail1_decoded

theorem exports_vector_decoded :
    vector exportEntry { bytes := artifactBytes, pos := 769, limit := 897 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 897, limit := 897 }) := by
  refine vector_eq_of_parts (length := 11)
    (itemsStart := { bytes := artifactBytes, pos := 770, limit := 897 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact exports_tail0_decoded

#print axioms exports_vector_decoded


end Project.EulerOutwardFaceStep.Artifact
