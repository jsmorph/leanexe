import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.RunningSum.ArtifactCode0
import Project.RunningSum.ArtifactCode1
import Project.RunningSum.ArtifactCode2
import Project.RunningSum.ArtifactCode3
import Project.RunningSum.ArtifactCode4
import Project.RunningSum.ArtifactCode5
import Project.RunningSum.ArtifactCode6
import Project.RunningSum.ArtifactCode7
import Project.RunningSum.ArtifactCode8
import Project.RunningSum.ArtifactCode9
import Project.RunningSum.ArtifactCode10
import Project.RunningSum.ArtifactCode11
import Project.RunningSum.ArtifactCode12
import Project.RunningSum.ArtifactCode13

namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail14 :
    Internal.vectorLoop code 0 { bytes := bytes, pos := 16553, limit := 16553 } =
      .ok (raw.core.codes.drop 14, { bytes := bytes, pos := 16553, limit := 16553 }) := by rfl

theorem codes_tail13 :
    Internal.vectorLoop code 1 { bytes := bytes, pos := 16252, limit := 16553 } =
      .ok (raw.core.codes.drop 13, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14

theorem codes_tail12 :
    Internal.vectorLoop code 2 { bytes := bytes, pos := 15899, limit := 16553 } =
      .ok (raw.core.codes.drop 12, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13

theorem codes_tail11 :
    Internal.vectorLoop code 3 { bytes := bytes, pos := 15890, limit := 16553 } =
      .ok (raw.core.codes.drop 11, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12

theorem codes_tail10 :
    Internal.vectorLoop code 4 { bytes := bytes, pos := 15632, limit := 16553 } =
      .ok (raw.core.codes.drop 10, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11

theorem codes_tail9 :
    Internal.vectorLoop code 5 { bytes := bytes, pos := 14961, limit := 16553 } =
      .ok (raw.core.codes.drop 9, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10

theorem codes_tail8 :
    Internal.vectorLoop code 6 { bytes := bytes, pos := 10437, limit := 16553 } =
      .ok (raw.core.codes.drop 8, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9

theorem codes_tail7 :
    Internal.vectorLoop code 7 { bytes := bytes, pos := 10013, limit := 16553 } =
      .ok (raw.core.codes.drop 7, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8

theorem codes_tail6 :
    Internal.vectorLoop code 8 { bytes := bytes, pos := 6678, limit := 16553 } =
      .ok (raw.core.codes.drop 6, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 9 { bytes := bytes, pos := 6373, limit := 16553 } =
      .ok (raw.core.codes.drop 5, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 10 { bytes := bytes, pos := 5654, limit := 16553 } =
      .ok (raw.core.codes.drop 4, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 11 { bytes := bytes, pos := 5631, limit := 16553 } =
      .ok (raw.core.codes.drop 3, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 12 { bytes := bytes, pos := 1730, limit := 16553 } =
      .ok (raw.core.codes.drop 2, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 13 { bytes := bytes, pos := 1719, limit := 16553 } =
      .ok (raw.core.codes.drop 1, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 14 { bytes := bytes, pos := 474, limit := 16553 } =
      .ok (raw.core.codes.drop 0, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := bytes, pos := 473, limit := 16553 } =
      .ok (raw.core.codes, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  refine vector_eq_of_parts (length := 14)
    (itemsStart := { bytes := bytes, pos := 474, limit := 16553 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := bytes, pos := 471, limit := 16553 } = .ok (raw.core.codes, { bytes := bytes, pos := 16553, limit := 16553 }) := by
  refine sized_eq_of_parts (size := 16080)
    (payload := { bytes := bytes, pos := 473, limit := 16553 }) (finish := { bytes := bytes, pos := 16553, limit := 16553 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.RunningSum.Artifact
