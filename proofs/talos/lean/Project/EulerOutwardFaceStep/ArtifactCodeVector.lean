import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardFaceStep.ArtifactCodes0To7
import Project.EulerOutwardFaceStep.ArtifactCodes8To15
import Project.EulerOutwardFaceStep.ArtifactCodes16To23
import Project.EulerOutwardFaceStep.ArtifactCodes24To31
import Project.EulerOutwardFaceStep.ArtifactCodes32To39
import Project.EulerOutwardFaceStep.ArtifactCodes40To47
import Project.EulerOutwardFaceStep.ArtifactCodes48To55
import Project.EulerOutwardFaceStep.ArtifactCodes56To63
import Project.EulerOutwardFaceStep.ArtifactCodes64To71
import Project.EulerOutwardFaceStep.ArtifactCodes72To74

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail75_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 9077, limit := 9077 } =
      .ok (Cache.raw.codes.drop 75, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by rfl

theorem codes_tail74_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 8724, limit := 9077 } =
      .ok (Cache.raw.codes.drop 74, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code74_decoded codes_tail75_decoded

theorem codes_tail73_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 8643, limit := 9077 } =
      .ok (Cache.raw.codes.drop 73, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code73_decoded codes_tail74_decoded

theorem codes_tail72_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 8615, limit := 9077 } =
      .ok (Cache.raw.codes.drop 72, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code72_decoded codes_tail73_decoded

theorem codes_tail71_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 8248, limit := 9077 } =
      .ok (Cache.raw.codes.drop 71, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code71_decoded codes_tail72_decoded

theorem codes_tail70_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 7902, limit := 9077 } =
      .ok (Cache.raw.codes.drop 70, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code70_decoded codes_tail71_decoded

theorem codes_tail69_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 7025, limit := 9077 } =
      .ok (Cache.raw.codes.drop 69, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code69_decoded codes_tail70_decoded

theorem codes_tail68_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 6972, limit := 9077 } =
      .ok (Cache.raw.codes.drop 68, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code68_decoded codes_tail69_decoded

theorem codes_tail67_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 6961, limit := 9077 } =
      .ok (Cache.raw.codes.drop 67, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code67_decoded codes_tail68_decoded

theorem codes_tail66_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 6950, limit := 9077 } =
      .ok (Cache.raw.codes.drop 66, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code66_decoded codes_tail67_decoded

theorem codes_tail65_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 6939, limit := 9077 } =
      .ok (Cache.raw.codes.drop 65, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code65_decoded codes_tail66_decoded

theorem codes_tail64_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 6928, limit := 9077 } =
      .ok (Cache.raw.codes.drop 64, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code64_decoded codes_tail65_decoded

theorem codes_tail63_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 6917, limit := 9077 } =
      .ok (Cache.raw.codes.drop 63, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code63_decoded codes_tail64_decoded

theorem codes_tail62_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 6870, limit := 9077 } =
      .ok (Cache.raw.codes.drop 62, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code62_decoded codes_tail63_decoded

theorem codes_tail61_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 6626, limit := 9077 } =
      .ok (Cache.raw.codes.drop 61, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code61_decoded codes_tail62_decoded

theorem codes_tail60_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 6615, limit := 9077 } =
      .ok (Cache.raw.codes.drop 60, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code60_decoded codes_tail61_decoded

theorem codes_tail59_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 6604, limit := 9077 } =
      .ok (Cache.raw.codes.drop 59, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code59_decoded codes_tail60_decoded

theorem codes_tail58_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 6593, limit := 9077 } =
      .ok (Cache.raw.codes.drop 58, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code58_decoded codes_tail59_decoded

theorem codes_tail57_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 6582, limit := 9077 } =
      .ok (Cache.raw.codes.drop 57, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code57_decoded codes_tail58_decoded

theorem codes_tail56_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 6571, limit := 9077 } =
      .ok (Cache.raw.codes.drop 56, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code56_decoded codes_tail57_decoded

theorem codes_tail55_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 6560, limit := 9077 } =
      .ok (Cache.raw.codes.drop 55, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code55_decoded codes_tail56_decoded

theorem codes_tail54_decoded :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 5904, limit := 9077 } =
      .ok (Cache.raw.codes.drop 54, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code54_decoded codes_tail55_decoded

theorem codes_tail53_decoded :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 5863, limit := 9077 } =
      .ok (Cache.raw.codes.drop 53, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code53_decoded codes_tail54_decoded

theorem codes_tail52_decoded :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 5852, limit := 9077 } =
      .ok (Cache.raw.codes.drop 52, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code52_decoded codes_tail53_decoded

theorem codes_tail51_decoded :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 5841, limit := 9077 } =
      .ok (Cache.raw.codes.drop 51, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code51_decoded codes_tail52_decoded

theorem codes_tail50_decoded :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 5830, limit := 9077 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code50_decoded codes_tail51_decoded

theorem codes_tail49_decoded :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 5819, limit := 9077 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50_decoded

theorem codes_tail48_decoded :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 5808, limit := 9077 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49_decoded

theorem codes_tail47_decoded :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 5797, limit := 9077 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48_decoded

theorem codes_tail46_decoded :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 5744, limit := 9077 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47_decoded

theorem codes_tail45_decoded :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 5382, limit := 9077 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46_decoded

theorem codes_tail44_decoded :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 5365, limit := 9077 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45_decoded

theorem codes_tail43_decoded :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 5328, limit := 9077 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44_decoded

theorem codes_tail42_decoded :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 5305, limit := 9077 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43_decoded

theorem codes_tail41_decoded :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 5263, limit := 9077 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42_decoded

theorem codes_tail40_decoded :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 5252, limit := 9077 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41_decoded

theorem codes_tail39_decoded :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 5241, limit := 9077 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40_decoded

theorem codes_tail38_decoded :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 4573, limit := 9077 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39_decoded

theorem codes_tail37_decoded :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 4520, limit := 9077 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38_decoded

theorem codes_tail36_decoded :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 4254, limit := 9077 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37_decoded

theorem codes_tail35_decoded :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 4135, limit := 9077 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36_decoded

theorem codes_tail34_decoded :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 4024, limit := 9077 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35_decoded

theorem codes_tail33_decoded :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 3812, limit := 9077 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34_decoded

theorem codes_tail32_decoded :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 3678, limit := 9077 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33_decoded

theorem codes_tail31_decoded :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 3559, limit := 9077 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32_decoded

theorem codes_tail30_decoded :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 3447, limit := 9077 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31_decoded

theorem codes_tail29_decoded :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 3096, limit := 9077 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30_decoded

theorem codes_tail28_decoded :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 3085, limit := 9077 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29_decoded

theorem codes_tail27_decoded :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 2973, limit := 9077 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28_decoded

theorem codes_tail26_decoded :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 2962, limit := 9077 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27_decoded

theorem codes_tail25_decoded :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 2850, limit := 9077 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26_decoded

theorem codes_tail24_decoded :
    Internal.vectorLoop code 51 { bytes := artifactBytes, pos := 2720, limit := 9077 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25_decoded

theorem codes_tail23_decoded :
    Internal.vectorLoop code 52 { bytes := artifactBytes, pos := 2593, limit := 9077 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24_decoded

theorem codes_tail22_decoded :
    Internal.vectorLoop code 53 { bytes := artifactBytes, pos := 2576, limit := 9077 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23_decoded

theorem codes_tail21_decoded :
    Internal.vectorLoop code 54 { bytes := artifactBytes, pos := 2520, limit := 9077 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22_decoded

theorem codes_tail20_decoded :
    Internal.vectorLoop code 55 { bytes := artifactBytes, pos := 2451, limit := 9077 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21_decoded

theorem codes_tail19_decoded :
    Internal.vectorLoop code 56 { bytes := artifactBytes, pos := 2382, limit := 9077 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 57 { bytes := artifactBytes, pos := 2299, limit := 9077 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 58 { bytes := artifactBytes, pos := 1968, limit := 9077 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 59 { bytes := artifactBytes, pos := 1832, limit := 9077 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 60 { bytes := artifactBytes, pos := 1764, limit := 9077 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 61 { bytes := artifactBytes, pos := 1648, limit := 9077 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 62 { bytes := artifactBytes, pos := 1573, limit := 9077 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 63 { bytes := artifactBytes, pos := 1514, limit := 9077 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 64 { bytes := artifactBytes, pos := 1482, limit := 9077 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 65 { bytes := artifactBytes, pos := 1400, limit := 9077 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 66 { bytes := artifactBytes, pos := 1301, limit := 9077 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 67 { bytes := artifactBytes, pos := 1255, limit := 9077 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 68 { bytes := artifactBytes, pos := 1233, limit := 9077 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 69 { bytes := artifactBytes, pos := 1196, limit := 9077 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 70 { bytes := artifactBytes, pos := 1173, limit := 9077 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 71 { bytes := artifactBytes, pos := 1131, limit := 9077 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded

theorem codes_tail3_decoded :
    Internal.vectorLoop code 72 { bytes := artifactBytes, pos := 1003, limit := 9077 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 73 { bytes := artifactBytes, pos := 966, limit := 9077 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 74 { bytes := artifactBytes, pos := 943, limit := 9077 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 75 { bytes := artifactBytes, pos := 901, limit := 9077 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 900, limit := 9077 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine vector_eq_of_parts (length := 75)
    (itemsStart := { bytes := artifactBytes, pos := 901, limit := 9077 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

#print axioms codes_vector_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 898, limit := 9077 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 9077, limit := 9077 }) := by
  refine sized_eq_of_parts (size := 8177)
    (payload := { bytes := artifactBytes, pos := 900, limit := 9077 }) (finish := { bytes := artifactBytes, pos := 9077, limit := 9077 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded


end Project.EulerOutwardFaceStep.Artifact
