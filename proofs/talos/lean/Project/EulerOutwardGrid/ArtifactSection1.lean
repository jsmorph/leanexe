import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactSection1Items0
import Project.EulerOutwardGrid.ArtifactSection1Items1
import Project.EulerOutwardGrid.ArtifactSection1Items2
import Project.EulerOutwardGrid.ArtifactSection1Items3

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_tail50 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 364, limit := 364 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 364, limit := 364 }) := by rfl

theorem types_tail49 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 360, limit := 364 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50

theorem types_tail48 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 355, limit := 364 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49

theorem types_tail47 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 352, limit := 364 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48

theorem types_tail46 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 347, limit := 364 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47

theorem types_tail45 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 341, limit := 364 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46

theorem types_tail44 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 327, limit := 364 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45

theorem types_tail43 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 313, limit := 364 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44

theorem types_tail42 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 304, limit := 364 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43

theorem types_tail41 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 296, limit := 364 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42

theorem types_tail40 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 288, limit := 364 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41

theorem types_tail39 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 280, limit := 364 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40

theorem types_tail38 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 272, limit := 364 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39

theorem types_tail37 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 263, limit := 364 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38

theorem types_tail36 :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 254, limit := 364 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37

theorem types_tail35 :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 247, limit := 364 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36

theorem types_tail34 :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 238, limit := 364 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35

theorem types_tail33 :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 229, limit := 364 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34

theorem types_tail32 :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 220, limit := 364 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33

theorem types_tail31 :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 212, limit := 364 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32

theorem types_tail30 :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 204, limit := 364 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31

theorem types_tail29 :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 196, limit := 364 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30

theorem types_tail28 :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 188, limit := 364 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29

theorem types_tail27 :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 180, limit := 364 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28

theorem types_tail26 :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 173, limit := 364 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27

theorem types_tail25 :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 167, limit := 364 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26

theorem types_tail24 :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 162, limit := 364 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25

theorem types_tail23 :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 157, limit := 364 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24

theorem types_tail22 :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 149, limit := 364 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23

theorem types_tail21 :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 141, limit := 364 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22

theorem types_tail20 :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 133, limit := 364 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21

theorem types_tail19 :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 127, limit := 364 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20

theorem types_tail18 :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 121, limit := 364 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19

theorem types_tail17 :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 113, limit := 364 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18

theorem types_tail16 :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 107, limit := 364 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17

theorem types_tail15 :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 101, limit := 364 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16

theorem types_tail14 :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 95, limit := 364 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15

theorem types_tail13 :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 87, limit := 364 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14

theorem types_tail12 :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 82, limit := 364 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 76, limit := 364 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 71, limit := 364 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 66, limit := 364 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 61, limit := 364 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 53, limit := 364 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 48, limit := 364 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 43, limit := 364 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 38, limit := 364 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 29, limit := 364 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 24, limit := 364 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 18, limit := 364 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 12, limit := 364 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 364 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 364, limit := 364 }) := by
  refine vector_eq_of_parts (length := 50)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 364 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 5720 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 364, limit := 5720 }) := by
  refine sized_eq_of_parts (size := 353)
    (payload := { bytes := artifactBytes, pos := 11, limit := 5720 }) (finish := { bytes := artifactBytes, pos := 364, limit := 364 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.EulerOutwardGrid.Artifact
