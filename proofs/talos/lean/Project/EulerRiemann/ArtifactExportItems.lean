import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem exports_item0_decoded :
    exportEntry { bytes := artifactBytes, pos := 1176, limit := 1289 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 1185, limit := 1289 }) := by
  cbv

theorem exports_item1_decoded :
    exportEntry { bytes := artifactBytes, pos := 1185, limit := 1289 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 1193, limit := 1289 }) := by
  cbv

theorem exports_item2_decoded :
    exportEntry { bytes := artifactBytes, pos := 1193, limit := 1289 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 1201, limit := 1289 }) := by
  cbv

theorem exports_item3_decoded :
    exportEntry { bytes := artifactBytes, pos := 1201, limit := 1289 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 1209, limit := 1289 }) := by
  cbv

theorem exports_item4_decoded :
    exportEntry { bytes := artifactBytes, pos := 1209, limit := 1289 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 1218, limit := 1289 }) := by
  cbv

theorem exports_item5_decoded :
    exportEntry { bytes := artifactBytes, pos := 1218, limit := 1289 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 1228, limit := 1289 }) := by
  cbv

theorem exports_item6_decoded :
    exportEntry { bytes := artifactBytes, pos := 1228, limit := 1289 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 1235, limit := 1289 }) := by
  cbv

theorem exports_item7_decoded :
    exportEntry { bytes := artifactBytes, pos := 1235, limit := 1289 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 1248, limit := 1289 }) := by
  cbv

theorem exports_item8_decoded :
    exportEntry { bytes := artifactBytes, pos := 1248, limit := 1289 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 1262, limit := 1289 }) := by
  cbv

theorem exports_item9_decoded :
    exportEntry { bytes := artifactBytes, pos := 1262, limit := 1289 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 1277, limit := 1289 }) := by
  cbv

theorem exports_item10_decoded :
    exportEntry { bytes := artifactBytes, pos := 1277, limit := 1289 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  cbv

theorem exports_tail11_decoded :
    Internal.vectorLoop (exportEntry) 0 { bytes := artifactBytes, pos := 1289, limit := 1289 } =
      .ok (Cache.raw.exports.drop 11, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by rfl

theorem exports_tail10_decoded :
    Internal.vectorLoop (exportEntry) 1 { bytes := artifactBytes, pos := 1277, limit := 1289 } =
      .ok (Cache.raw.exports.drop 10, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item10_decoded exports_tail11_decoded

theorem exports_tail9_decoded :
    Internal.vectorLoop (exportEntry) 2 { bytes := artifactBytes, pos := 1262, limit := 1289 } =
      .ok (Cache.raw.exports.drop 9, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item9_decoded exports_tail10_decoded

theorem exports_tail8_decoded :
    Internal.vectorLoop (exportEntry) 3 { bytes := artifactBytes, pos := 1248, limit := 1289 } =
      .ok (Cache.raw.exports.drop 8, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item8_decoded exports_tail9_decoded

theorem exports_tail7_decoded :
    Internal.vectorLoop (exportEntry) 4 { bytes := artifactBytes, pos := 1235, limit := 1289 } =
      .ok (Cache.raw.exports.drop 7, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item7_decoded exports_tail8_decoded

theorem exports_tail6_decoded :
    Internal.vectorLoop (exportEntry) 5 { bytes := artifactBytes, pos := 1228, limit := 1289 } =
      .ok (Cache.raw.exports.drop 6, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item6_decoded exports_tail7_decoded

theorem exports_tail5_decoded :
    Internal.vectorLoop (exportEntry) 6 { bytes := artifactBytes, pos := 1218, limit := 1289 } =
      .ok (Cache.raw.exports.drop 5, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item5_decoded exports_tail6_decoded

theorem exports_tail4_decoded :
    Internal.vectorLoop (exportEntry) 7 { bytes := artifactBytes, pos := 1209, limit := 1289 } =
      .ok (Cache.raw.exports.drop 4, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item4_decoded exports_tail5_decoded

theorem exports_tail3_decoded :
    Internal.vectorLoop (exportEntry) 8 { bytes := artifactBytes, pos := 1201, limit := 1289 } =
      .ok (Cache.raw.exports.drop 3, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item3_decoded exports_tail4_decoded

theorem exports_tail2_decoded :
    Internal.vectorLoop (exportEntry) 9 { bytes := artifactBytes, pos := 1193, limit := 1289 } =
      .ok (Cache.raw.exports.drop 2, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item2_decoded exports_tail3_decoded

theorem exports_tail1_decoded :
    Internal.vectorLoop (exportEntry) 10 { bytes := artifactBytes, pos := 1185, limit := 1289 } =
      .ok (Cache.raw.exports.drop 1, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item1_decoded exports_tail2_decoded

theorem exports_tail0_decoded :
    Internal.vectorLoop (exportEntry) 11 { bytes := artifactBytes, pos := 1176, limit := 1289 } =
      .ok (Cache.raw.exports.drop 0, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  exact vectorLoop_eq_cons exports_item0_decoded exports_tail1_decoded

theorem exports_vector_decoded :
    vector (exportEntry) { bytes := artifactBytes, pos := 1175, limit := 1289 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 1289, limit := 1289 }) := by
  refine vector_eq_of_parts (length := 11) (itemsStart := { bytes := artifactBytes, pos := 1176, limit := 1289 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact exports_tail0_decoded

#print axioms exports_vector_decoded

end Project.EulerRiemann.Artifact
