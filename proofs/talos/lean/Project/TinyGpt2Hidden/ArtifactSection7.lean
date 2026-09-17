import Project.TinyGpt2Hidden.ArtifactExportSlices
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem exports_item0 :
    exportEntry { bytes := artifactBytes, pos := 943, limit := 1057 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 952, limit := 1057 }) := by cbv

theorem exports_item1 :
    exportEntry { bytes := artifactBytes, pos := 952, limit := 1057 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 961, limit := 1057 }) := by cbv

theorem exports_item2 :
    exportEntry { bytes := artifactBytes, pos := 961, limit := 1057 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 969, limit := 1057 }) := by cbv

theorem exports_item3 :
    exportEntry { bytes := artifactBytes, pos := 969, limit := 1057 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 977, limit := 1057 }) := by cbv

theorem exports_item4 :
    exportEntry { bytes := artifactBytes, pos := 977, limit := 1057 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 986, limit := 1057 }) := by cbv

theorem exports_item5 :
    exportEntry { bytes := artifactBytes, pos := 986, limit := 1057 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 996, limit := 1057 }) := by cbv

theorem exports_item6 :
    exportEntry { bytes := artifactBytes, pos := 996, limit := 1057 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 1003, limit := 1057 }) := by cbv

theorem exports_item7 :
    exportEntry { bytes := artifactBytes, pos := 1003, limit := 1057 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 1016, limit := 1057 }) := by cbv

theorem exports_item8 :
    exportEntry { bytes := artifactBytes, pos := 1016, limit := 1057 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 1030, limit := 1057 }) := by cbv

theorem exports_item9 :
    exportEntry { bytes := artifactBytes, pos := 1030, limit := 1057 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 1045, limit := 1057 }) := by cbv

theorem exports_item10 :
    exportEntry { bytes := artifactBytes, pos := 1045, limit := 1057 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by cbv

theorem exports_tail11 :
    Internal.vectorLoop exportEntry 0 { bytes := artifactBytes, pos := 1057, limit := 1057 } =
      .ok (Cache.raw.exports.drop 11, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by rfl

theorem exports_tail10 :
    Internal.vectorLoop exportEntry 1 { bytes := artifactBytes, pos := 1045, limit := 1057 } =
      .ok (Cache.raw.exports.drop 10, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item10 exports_tail11

theorem exports_tail9 :
    Internal.vectorLoop exportEntry 2 { bytes := artifactBytes, pos := 1030, limit := 1057 } =
      .ok (Cache.raw.exports.drop 9, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item9 exports_tail10

theorem exports_tail8 :
    Internal.vectorLoop exportEntry 3 { bytes := artifactBytes, pos := 1016, limit := 1057 } =
      .ok (Cache.raw.exports.drop 8, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item8 exports_tail9

theorem exports_tail7 :
    Internal.vectorLoop exportEntry 4 { bytes := artifactBytes, pos := 1003, limit := 1057 } =
      .ok (Cache.raw.exports.drop 7, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item7 exports_tail8

theorem exports_tail6 :
    Internal.vectorLoop exportEntry 5 { bytes := artifactBytes, pos := 996, limit := 1057 } =
      .ok (Cache.raw.exports.drop 6, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item6 exports_tail7

theorem exports_tail5 :
    Internal.vectorLoop exportEntry 6 { bytes := artifactBytes, pos := 986, limit := 1057 } =
      .ok (Cache.raw.exports.drop 5, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item5 exports_tail6

theorem exports_tail4 :
    Internal.vectorLoop exportEntry 7 { bytes := artifactBytes, pos := 977, limit := 1057 } =
      .ok (Cache.raw.exports.drop 4, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item4 exports_tail5

theorem exports_tail3 :
    Internal.vectorLoop exportEntry 8 { bytes := artifactBytes, pos := 969, limit := 1057 } =
      .ok (Cache.raw.exports.drop 3, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item3 exports_tail4

theorem exports_tail2 :
    Internal.vectorLoop exportEntry 9 { bytes := artifactBytes, pos := 961, limit := 1057 } =
      .ok (Cache.raw.exports.drop 2, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item2 exports_tail3

theorem exports_tail1 :
    Internal.vectorLoop exportEntry 10 { bytes := artifactBytes, pos := 952, limit := 1057 } =
      .ok (Cache.raw.exports.drop 1, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item1 exports_tail2

theorem exports_tail0 :
    Internal.vectorLoop exportEntry 11 { bytes := artifactBytes, pos := 943, limit := 1057 } =
      .ok (Cache.raw.exports.drop 0, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  exact vectorLoop_eq_cons exports_item0 exports_tail1

theorem exports_vector :
    vector exportEntry { bytes := artifactBytes, pos := 942, limit := 1057 } = .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 1057, limit := 1057 }) := by
  refine vector_eq_of_parts (length := 11) (itemsStart := { bytes := artifactBytes, pos := 943, limit := 1057 }) ?_ ?_ exports_tail0
  · cbv
  · decide

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 941, limit := 16006 } = .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 1057, limit := 16006 }) := by
  refine sized_eq_of_parts (size := 115) (payload := { bytes := artifactBytes, pos := 942, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 1057, limit := 1057 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector
  · rfl

#print axioms exports_section_decoded
end Project.TinyGpt2Hidden.Artifact
