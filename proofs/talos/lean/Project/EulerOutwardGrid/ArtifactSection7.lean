import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem export0_decoded :
    exportEntry { bytes := artifactBytes, pos := 459, limit := 576 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 468, limit := 576 }) := by cbv

#print axioms export0_decoded

theorem export1_decoded :
    exportEntry { bytes := artifactBytes, pos := 468, limit := 576 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 480, limit := 576 }) := by cbv

#print axioms export1_decoded

theorem export2_decoded :
    exportEntry { bytes := artifactBytes, pos := 480, limit := 576 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 488, limit := 576 }) := by cbv

#print axioms export2_decoded

theorem export3_decoded :
    exportEntry { bytes := artifactBytes, pos := 488, limit := 576 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 496, limit := 576 }) := by cbv

#print axioms export3_decoded

theorem export4_decoded :
    exportEntry { bytes := artifactBytes, pos := 496, limit := 576 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 505, limit := 576 }) := by cbv

#print axioms export4_decoded

theorem export5_decoded :
    exportEntry { bytes := artifactBytes, pos := 505, limit := 576 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 515, limit := 576 }) := by cbv

#print axioms export5_decoded

theorem export6_decoded :
    exportEntry { bytes := artifactBytes, pos := 515, limit := 576 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 522, limit := 576 }) := by cbv

#print axioms export6_decoded

theorem export7_decoded :
    exportEntry { bytes := artifactBytes, pos := 522, limit := 576 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 535, limit := 576 }) := by cbv

#print axioms export7_decoded

theorem export8_decoded :
    exportEntry { bytes := artifactBytes, pos := 535, limit := 576 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 549, limit := 576 }) := by cbv

#print axioms export8_decoded

theorem export9_decoded :
    exportEntry { bytes := artifactBytes, pos := 549, limit := 576 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 564, limit := 576 }) := by cbv

#print axioms export9_decoded

theorem export10_decoded :
    exportEntry { bytes := artifactBytes, pos := 564, limit := 576 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 576, limit := 576 }) := by cbv

#print axioms export10_decoded

theorem exports_tail11 :
    Internal.vectorLoop exportEntry 0 { bytes := artifactBytes, pos := 576, limit := 576 } =
      .ok (Cache.raw.exports.drop 11, { bytes := artifactBytes, pos := 576, limit := 576 }) := by rfl

theorem exports_tail10 :
    Internal.vectorLoop exportEntry 1 { bytes := artifactBytes, pos := 564, limit := 576 } =
      .ok (Cache.raw.exports.drop 10, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export10_decoded exports_tail11

theorem exports_tail9 :
    Internal.vectorLoop exportEntry 2 { bytes := artifactBytes, pos := 549, limit := 576 } =
      .ok (Cache.raw.exports.drop 9, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export9_decoded exports_tail10

theorem exports_tail8 :
    Internal.vectorLoop exportEntry 3 { bytes := artifactBytes, pos := 535, limit := 576 } =
      .ok (Cache.raw.exports.drop 8, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export8_decoded exports_tail9

theorem exports_tail7 :
    Internal.vectorLoop exportEntry 4 { bytes := artifactBytes, pos := 522, limit := 576 } =
      .ok (Cache.raw.exports.drop 7, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export7_decoded exports_tail8

theorem exports_tail6 :
    Internal.vectorLoop exportEntry 5 { bytes := artifactBytes, pos := 515, limit := 576 } =
      .ok (Cache.raw.exports.drop 6, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export6_decoded exports_tail7

theorem exports_tail5 :
    Internal.vectorLoop exportEntry 6 { bytes := artifactBytes, pos := 505, limit := 576 } =
      .ok (Cache.raw.exports.drop 5, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export5_decoded exports_tail6

theorem exports_tail4 :
    Internal.vectorLoop exportEntry 7 { bytes := artifactBytes, pos := 496, limit := 576 } =
      .ok (Cache.raw.exports.drop 4, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export4_decoded exports_tail5

theorem exports_tail3 :
    Internal.vectorLoop exportEntry 8 { bytes := artifactBytes, pos := 488, limit := 576 } =
      .ok (Cache.raw.exports.drop 3, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export3_decoded exports_tail4

theorem exports_tail2 :
    Internal.vectorLoop exportEntry 9 { bytes := artifactBytes, pos := 480, limit := 576 } =
      .ok (Cache.raw.exports.drop 2, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export2_decoded exports_tail3

theorem exports_tail1 :
    Internal.vectorLoop exportEntry 10 { bytes := artifactBytes, pos := 468, limit := 576 } =
      .ok (Cache.raw.exports.drop 1, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export1_decoded exports_tail2

theorem exports_tail0 :
    Internal.vectorLoop exportEntry 11 { bytes := artifactBytes, pos := 459, limit := 576 } =
      .ok (Cache.raw.exports.drop 0, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  exact vectorLoop_eq_cons export0_decoded exports_tail1

theorem exports_vector_decoded :
    vector exportEntry { bytes := artifactBytes, pos := 458, limit := 576 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 576, limit := 576 }) := by
  refine vector_eq_of_parts (length := 11)
    (itemsStart := { bytes := artifactBytes, pos := 459, limit := 576 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact exports_tail0

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 457, limit := 5720 } = .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 576, limit := 5720 }) := by
  refine sized_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 458, limit := 5720 }) (finish := { bytes := artifactBytes, pos := 576, limit := 576 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded

end Project.EulerOutwardGrid.Artifact
