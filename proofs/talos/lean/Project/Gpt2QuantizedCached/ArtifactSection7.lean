import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem export0_decoded :
    exportEntry { bytes := artifactBytes, pos := 646, limit := 780 } =
      .ok (Cache.raw.exports[0]!, { bytes := artifactBytes, pos := 655, limit := 780 }) := by cbv

theorem export1_decoded :
    exportEntry { bytes := artifactBytes, pos := 655, limit := 780 } =
      .ok (Cache.raw.exports[1]!, { bytes := artifactBytes, pos := 671, limit := 780 }) := by cbv

theorem export2_decoded :
    exportEntry { bytes := artifactBytes, pos := 671, limit := 780 } =
      .ok (Cache.raw.exports[2]!, { bytes := artifactBytes, pos := 684, limit := 780 }) := by cbv

theorem export3_decoded :
    exportEntry { bytes := artifactBytes, pos := 684, limit := 780 } =
      .ok (Cache.raw.exports[3]!, { bytes := artifactBytes, pos := 692, limit := 780 }) := by cbv

theorem export4_decoded :
    exportEntry { bytes := artifactBytes, pos := 692, limit := 780 } =
      .ok (Cache.raw.exports[4]!, { bytes := artifactBytes, pos := 700, limit := 780 }) := by cbv

theorem export5_decoded :
    exportEntry { bytes := artifactBytes, pos := 700, limit := 780 } =
      .ok (Cache.raw.exports[5]!, { bytes := artifactBytes, pos := 709, limit := 780 }) := by cbv

theorem export6_decoded :
    exportEntry { bytes := artifactBytes, pos := 709, limit := 780 } =
      .ok (Cache.raw.exports[6]!, { bytes := artifactBytes, pos := 719, limit := 780 }) := by cbv

theorem export7_decoded :
    exportEntry { bytes := artifactBytes, pos := 719, limit := 780 } =
      .ok (Cache.raw.exports[7]!, { bytes := artifactBytes, pos := 726, limit := 780 }) := by cbv

theorem export8_decoded :
    exportEntry { bytes := artifactBytes, pos := 726, limit := 780 } =
      .ok (Cache.raw.exports[8]!, { bytes := artifactBytes, pos := 739, limit := 780 }) := by cbv

theorem export9_decoded :
    exportEntry { bytes := artifactBytes, pos := 739, limit := 780 } =
      .ok (Cache.raw.exports[9]!, { bytes := artifactBytes, pos := 753, limit := 780 }) := by cbv

theorem export10_decoded :
    exportEntry { bytes := artifactBytes, pos := 753, limit := 780 } =
      .ok (Cache.raw.exports[10]!, { bytes := artifactBytes, pos := 768, limit := 780 }) := by cbv

theorem export11_decoded :
    exportEntry { bytes := artifactBytes, pos := 768, limit := 780 } =
      .ok (Cache.raw.exports[11]!, { bytes := artifactBytes, pos := 780, limit := 780 }) := by cbv

theorem exports_tail12 :
    Internal.vectorLoop exportEntry 0 { bytes := artifactBytes, pos := 780, limit := 780 } =
      .ok (Cache.raw.exports.drop 12, { bytes := artifactBytes, pos := 780, limit := 780 }) := by rfl

theorem exports_tail11 :
    Internal.vectorLoop exportEntry 1 { bytes := artifactBytes, pos := 768, limit := 780 } =
      .ok (Cache.raw.exports.drop 11, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export11_decoded exports_tail12

theorem exports_tail10 :
    Internal.vectorLoop exportEntry 2 { bytes := artifactBytes, pos := 753, limit := 780 } =
      .ok (Cache.raw.exports.drop 10, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export10_decoded exports_tail11

theorem exports_tail9 :
    Internal.vectorLoop exportEntry 3 { bytes := artifactBytes, pos := 739, limit := 780 } =
      .ok (Cache.raw.exports.drop 9, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export9_decoded exports_tail10

theorem exports_tail8 :
    Internal.vectorLoop exportEntry 4 { bytes := artifactBytes, pos := 726, limit := 780 } =
      .ok (Cache.raw.exports.drop 8, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export8_decoded exports_tail9

theorem exports_tail7 :
    Internal.vectorLoop exportEntry 5 { bytes := artifactBytes, pos := 719, limit := 780 } =
      .ok (Cache.raw.exports.drop 7, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export7_decoded exports_tail8

theorem exports_tail6 :
    Internal.vectorLoop exportEntry 6 { bytes := artifactBytes, pos := 709, limit := 780 } =
      .ok (Cache.raw.exports.drop 6, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export6_decoded exports_tail7

theorem exports_tail5 :
    Internal.vectorLoop exportEntry 7 { bytes := artifactBytes, pos := 700, limit := 780 } =
      .ok (Cache.raw.exports.drop 5, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export5_decoded exports_tail6

theorem exports_tail4 :
    Internal.vectorLoop exportEntry 8 { bytes := artifactBytes, pos := 692, limit := 780 } =
      .ok (Cache.raw.exports.drop 4, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export4_decoded exports_tail5

theorem exports_tail3 :
    Internal.vectorLoop exportEntry 9 { bytes := artifactBytes, pos := 684, limit := 780 } =
      .ok (Cache.raw.exports.drop 3, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export3_decoded exports_tail4

theorem exports_tail2 :
    Internal.vectorLoop exportEntry 10 { bytes := artifactBytes, pos := 671, limit := 780 } =
      .ok (Cache.raw.exports.drop 2, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export2_decoded exports_tail3

theorem exports_tail1 :
    Internal.vectorLoop exportEntry 11 { bytes := artifactBytes, pos := 655, limit := 780 } =
      .ok (Cache.raw.exports.drop 1, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export1_decoded exports_tail2

theorem exports_tail0 :
    Internal.vectorLoop exportEntry 12 { bytes := artifactBytes, pos := 646, limit := 780 } =
      .ok (Cache.raw.exports.drop 0, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  exact vectorLoop_eq_cons export0_decoded exports_tail1

theorem exports_vector_decoded :
    vector exportEntry { bytes := artifactBytes, pos := 645, limit := 780 } =
      .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 780, limit := 780 }) := by
  refine vector_eq_of_parts (length := 12)
    (itemsStart := { bytes := artifactBytes, pos := 646, limit := 780 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact exports_tail0

theorem exports_section_decoded :
    sized (vector exportEntry) { bytes := artifactBytes, pos := 643, limit := 28315 } = .ok (Cache.raw.exports, { bytes := artifactBytes, pos := 780, limit := 28315 }) := by
  refine sized_eq_of_parts (size := 135)
    (payload := { bytes := artifactBytes, pos := 645, limit := 28315 }) (finish := { bytes := artifactBytes, pos := 780, limit := 780 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact exports_vector_decoded
  · rfl

#print axioms exports_section_decoded

end Project.Gpt2QuantizedCached.Artifact
