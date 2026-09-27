import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0
import Project.ExpArm.ArtifactCode1
import Project.ExpArm.ArtifactCode2
import Project.ExpArm.ArtifactCode3
import Project.ExpArm.ArtifactCode4
import Project.ExpArm.ArtifactCode5
import Project.ExpArm.ArtifactCode6

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail7 :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 10666, limit := 10666 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by rfl

theorem codes_tail6 :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 10313, limit := 10666 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 10232, limit := 10666 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 10204, limit := 10666 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 9837, limit := 10666 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 9305, limit := 10666 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 9057, limit := 10666 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 212, limit := 10666 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 211, limit := 10666 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  refine vector_eq_of_parts (length := 7)
    (itemsStart := { bytes := artifactBytes, pos := 212, limit := 10666 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 209, limit := 12733 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 10666, limit := 12733 }) := by
  refine sized_eq_of_parts (size := 10455)
    (payload := { bytes := artifactBytes, pos := 211, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 10666, limit := 10666 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.ExpArm.Artifact
