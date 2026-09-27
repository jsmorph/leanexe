import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardCfl.ArtifactCodes0To7
import Project.EulerOutwardCfl.ArtifactCodes8To15
import Project.EulerOutwardCfl.ArtifactCodes16To19

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail20_decoded :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 2557, limit := 2557 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by rfl

theorem codes_tail19_decoded :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 2204, limit := 2557 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20_decoded

theorem codes_tail18_decoded :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 2123, limit := 2557 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19_decoded

theorem codes_tail17_decoded :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 2095, limit := 2557 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18_decoded

theorem codes_tail16_decoded :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 1728, limit := 2557 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17_decoded

theorem codes_tail15_decoded :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 1585, limit := 2557 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16_decoded

theorem codes_tail14_decoded :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 1291, limit := 2557 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15_decoded

theorem codes_tail13_decoded :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 1280, limit := 2557 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14_decoded

theorem codes_tail12_decoded :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 1168, limit := 2557 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13_decoded

theorem codes_tail11_decoded :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 1126, limit := 2557 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12_decoded

theorem codes_tail10_decoded :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 1115, limit := 2557 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11_decoded

theorem codes_tail9_decoded :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 1056, limit := 2557 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10_decoded

theorem codes_tail8_decoded :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 847, limit := 2557 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9_decoded

theorem codes_tail7_decoded :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 717, limit := 2557 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8_decoded

theorem codes_tail6_decoded :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 590, limit := 2557 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7_decoded

theorem codes_tail5_decoded :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 573, limit := 2557 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6_decoded

theorem codes_tail4_decoded :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 517, limit := 2557 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5_decoded

theorem codes_tail3_decoded :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 448, limit := 2557 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4_decoded

theorem codes_tail2_decoded :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 379, limit := 2557 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3_decoded

theorem codes_tail1_decoded :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 342, limit := 2557 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2_decoded

theorem codes_tail0_decoded :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 319, limit := 2557 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1_decoded

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 318, limit := 2557 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine vector_eq_of_parts (length := 20)
    (itemsStart := { bytes := artifactBytes, pos := 319, limit := 2557 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0_decoded

#print axioms codes_vector_decoded

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 316, limit := 2557 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine sized_eq_of_parts (size := 2239)
    (payload := { bytes := artifactBytes, pos := 318, limit := 2557 }) (finish := { bytes := artifactBytes, pos := 2557, limit := 2557 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded


end Project.EulerOutwardCfl.Artifact
