import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactCodes0To7
import Project.EulerOutwardGrid.ArtifactCodes8To15
import Project.EulerOutwardGrid.ArtifactCodes16To23
import Project.EulerOutwardGrid.ArtifactCodes24To31
import Project.EulerOutwardGrid.ArtifactCodes32To39
import Project.EulerOutwardGrid.ArtifactCodes40To47
import Project.EulerOutwardGrid.ArtifactCodes48To49

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail50_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 5728, limit := 5728 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by rfl

theorem codes_tail49_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 5375, limit := 5728 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50_decoded

theorem codes_tail48_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 5294, limit := 5728 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49_decoded

theorem codes_tail47_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 5266, limit := 5728 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48_decoded

theorem codes_tail46_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 4899, limit := 5728 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47_decoded

theorem codes_tail45_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 4565, limit := 5728 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46_decoded

theorem codes_tail44_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 4488, limit := 5728 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45_decoded

theorem codes_tail43_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 4459, limit := 5728 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44_decoded

theorem codes_tail42_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 4352, limit := 5728 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43_decoded

theorem codes_tail41_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 4341, limit := 5728 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42_decoded

theorem codes_tail40_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 4330, limit := 5728 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41_decoded

theorem codes_tail39_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 4319, limit := 5728 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40_decoded

theorem codes_tail38_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 4308, limit := 5728 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39_decoded

theorem codes_tail37_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 4042, limit := 5728 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38_decoded

theorem codes_tail36_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 3923, limit := 5728 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37_decoded

theorem codes_tail35_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 3812, limit := 5728 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36_decoded

theorem codes_tail34_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 3600, limit := 5728 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35_decoded

theorem codes_tail33_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 3466, limit := 5728 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34_decoded

theorem codes_tail32_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 3347, limit := 5728 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33_decoded

theorem codes_tail31_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 3235, limit := 5728 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32_decoded

theorem codes_tail30_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 2884, limit := 5728 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31_decoded

theorem codes_tail29_decoded :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 2772, limit := 5728 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30_decoded

theorem codes_tail28_decoded :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 2660, limit := 5728 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29_decoded

theorem codes_tail27_decoded :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 2530, limit := 5728 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28_decoded

theorem codes_tail26_decoded :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 2403, limit := 5728 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27_decoded

theorem codes_tail25_decoded :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 2347, limit := 5728 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26_decoded

theorem codes_tail24_decoded :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 2278, limit := 5728 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25_decoded

theorem codes_tail23_decoded :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 2209, limit := 5728 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24_decoded

theorem codes_tail22_decoded :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 2126, limit := 5728 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23_decoded

theorem codes_tail21_decoded :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 1795, limit := 5728 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22_decoded

theorem codes_tail20_decoded :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 1659, limit := 5728 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21_decoded

theorem codes_tail19_decoded :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 1591, limit := 5728 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 1475, limit := 5728 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 1400, limit := 5728 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 1341, limit := 5728 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 1309, limit := 5728 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 1227, limit := 5728 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 1128, limit := 5728 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 1082, limit := 5728 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 1060, limit := 5728 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 1023, limit := 5728 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 1000, limit := 5728 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 958, limit := 5728 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 830, limit := 5728 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 793, limit := 5728 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 770, limit := 5728 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 728, limit := 5728 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded

theorem codes_tail3_decoded :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 619, limit := 5728 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 602, limit := 5728 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 591, limit := 5728 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 580, limit := 5728 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 579, limit := 5728 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine vector_eq_of_parts (length := 50)
    (itemsStart := { bytes := artifactBytes, pos := 580, limit := 5728 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

#print axioms codes_vector_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 577, limit := 5728 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine sized_eq_of_parts (size := 5149)
    (payload := { bytes := artifactBytes, pos := 579, limit := 5728 }) (finish := { bytes := artifactBytes, pos := 5728, limit := 5728 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded


end Project.EulerOutwardGrid.Artifact
