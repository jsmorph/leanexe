import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactSection1Items0
import Project.Beck.ArtifactSection1Items1
import Project.Beck.ArtifactSection1Items2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_tail40 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 419, limit := 419 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 419, limit := 419 }) := by rfl

theorem types_tail39 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 415, limit := 419 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40

theorem types_tail38 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 410, limit := 419 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39

theorem types_tail37 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 407, limit := 419 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38

theorem types_tail36 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 402, limit := 419 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37

theorem types_tail35 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 397, limit := 419 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36

theorem types_tail34 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 381, limit := 419 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35

theorem types_tail33 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 366, limit := 419 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34

theorem types_tail32 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 350, limit := 419 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33

theorem types_tail31 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 343, limit := 419 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32

theorem types_tail30 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 329, limit := 419 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31

theorem types_tail29 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 320, limit := 419 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30

theorem types_tail28 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 305, limit := 419 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29

theorem types_tail27 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 288, limit := 419 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28

theorem types_tail26 :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 272, limit := 419 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27

theorem types_tail25 :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 253, limit := 419 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26

theorem types_tail24 :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 241, limit := 419 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25

theorem types_tail23 :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 233, limit := 419 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24

theorem types_tail22 :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 223, limit := 419 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23

theorem types_tail21 :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 213, limit := 419 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22

theorem types_tail20 :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 206, limit := 419 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21

theorem types_tail19 :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 192, limit := 419 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20

theorem types_tail18 :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 182, limit := 419 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19

theorem types_tail17 :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 168, limit := 419 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18

theorem types_tail16 :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 157, limit := 419 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17

theorem types_tail15 :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 147, limit := 419 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16

theorem types_tail14 :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 137, limit := 419 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15

theorem types_tail13 :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 130, limit := 419 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14

theorem types_tail12 :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 122, limit := 419 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 115, limit := 419 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 110, limit := 419 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 105, limit := 419 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 97, limit := 419 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 87, limit := 419 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 76, limit := 419 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 60, limit := 419 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 51, limit := 419 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 43, limit := 419 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 30, limit := 419 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 22, limit := 419 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 12, limit := 419 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 419 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 419, limit := 419 }) := by
  refine vector_eq_of_parts (length := 40)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 419 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 27068 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 419, limit := 27068 }) := by
  refine sized_eq_of_parts (size := 408)
    (payload := { bytes := artifactBytes, pos := 11, limit := 27068 }) (finish := { bytes := artifactBytes, pos := 419, limit := 419 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.Beck.Artifact
