import Project.Gpt2QuantizedCached.ArtifactSection1Items0
import Project.Gpt2QuantizedCached.ArtifactSection1Items1
import Project.Gpt2QuantizedCached.ArtifactSection1Items2
import Project.Gpt2QuantizedCached.ArtifactSection1Items3
import Project.Gpt2QuantizedCached.ArtifactSection1Items4
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_tail66 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 534, limit := 534 } =
      .ok (Cache.raw.types.drop 66, { bytes := artifactBytes, pos := 534, limit := 534 }) := by rfl

theorem types_tail65 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 530, limit := 534 } =
      .ok (Cache.raw.types.drop 65, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type65_decoded types_tail66

theorem types_tail64 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 525, limit := 534 } =
      .ok (Cache.raw.types.drop 64, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type64_decoded types_tail65

theorem types_tail63 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 522, limit := 534 } =
      .ok (Cache.raw.types.drop 63, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type63_decoded types_tail64

theorem types_tail62 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 517, limit := 534 } =
      .ok (Cache.raw.types.drop 62, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type62_decoded types_tail63

theorem types_tail61 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 503, limit := 534 } =
      .ok (Cache.raw.types.drop 61, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type61_decoded types_tail62

theorem types_tail60 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 497, limit := 534 } =
      .ok (Cache.raw.types.drop 60, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type60_decoded types_tail61

theorem types_tail59 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 479, limit := 534 } =
      .ok (Cache.raw.types.drop 59, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type59_decoded types_tail60

theorem types_tail58 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 461, limit := 534 } =
      .ok (Cache.raw.types.drop 58, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type58_decoded types_tail59

theorem types_tail57 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 448, limit := 534 } =
      .ok (Cache.raw.types.drop 57, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type57_decoded types_tail58

theorem types_tail56 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 435, limit := 534 } =
      .ok (Cache.raw.types.drop 56, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type56_decoded types_tail57

theorem types_tail55 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 424, limit := 534 } =
      .ok (Cache.raw.types.drop 55, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type55_decoded types_tail56

theorem types_tail54 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 403, limit := 534 } =
      .ok (Cache.raw.types.drop 54, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type54_decoded types_tail55

theorem types_tail53 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 394, limit := 534 } =
      .ok (Cache.raw.types.drop 53, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type53_decoded types_tail54

theorem types_tail52 :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 389, limit := 534 } =
      .ok (Cache.raw.types.drop 52, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type52_decoded types_tail53

theorem types_tail51 :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 377, limit := 534 } =
      .ok (Cache.raw.types.drop 51, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type51_decoded types_tail52

theorem types_tail50 :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 363, limit := 534 } =
      .ok (Cache.raw.types.drop 50, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type50_decoded types_tail51

theorem types_tail49 :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 354, limit := 534 } =
      .ok (Cache.raw.types.drop 49, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type49_decoded types_tail50

theorem types_tail48 :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 349, limit := 534 } =
      .ok (Cache.raw.types.drop 48, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type48_decoded types_tail49

theorem types_tail47 :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 344, limit := 534 } =
      .ok (Cache.raw.types.drop 47, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type47_decoded types_tail48

theorem types_tail46 :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 335, limit := 534 } =
      .ok (Cache.raw.types.drop 46, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type46_decoded types_tail47

theorem types_tail45 :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 329, limit := 534 } =
      .ok (Cache.raw.types.drop 45, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type45_decoded types_tail46

theorem types_tail44 :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 315, limit := 534 } =
      .ok (Cache.raw.types.drop 44, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type44_decoded types_tail45

theorem types_tail43 :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 301, limit := 534 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type43_decoded types_tail44

theorem types_tail42 :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 282, limit := 534 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43

theorem types_tail41 :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 270, limit := 534 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42

theorem types_tail40 :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 263, limit := 534 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41

theorem types_tail39 :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 251, limit := 534 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40

theorem types_tail38 :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 238, limit := 534 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39

theorem types_tail37 :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 224, limit := 534 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38

theorem types_tail36 :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 218, limit := 534 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37

theorem types_tail35 :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 209, limit := 534 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36

theorem types_tail34 :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 194, limit := 534 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35

theorem types_tail33 :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 185, limit := 534 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34

theorem types_tail32 :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 177, limit := 534 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33

theorem types_tail31 :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 169, limit := 534 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32

theorem types_tail30 :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 158, limit := 534 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31

theorem types_tail29 :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 154, limit := 534 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30

theorem types_tail28 :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 147, limit := 534 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29

theorem types_tail27 :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 139, limit := 534 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28

theorem types_tail26 :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 130, limit := 534 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27

theorem types_tail25 :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 125, limit := 534 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26

theorem types_tail24 :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 116, limit := 534 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25

theorem types_tail23 :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 107, limit := 534 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24

theorem types_tail22 :
    Internal.vectorLoop funcType 44 { bytes := artifactBytes, pos := 100, limit := 534 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23

theorem types_tail21 :
    Internal.vectorLoop funcType 45 { bytes := artifactBytes, pos := 96, limit := 534 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22

theorem types_tail20 :
    Internal.vectorLoop funcType 46 { bytes := artifactBytes, pos := 92, limit := 534 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21

theorem types_tail19 :
    Internal.vectorLoop funcType 47 { bytes := artifactBytes, pos := 88, limit := 534 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20

theorem types_tail18 :
    Internal.vectorLoop funcType 48 { bytes := artifactBytes, pos := 84, limit := 534 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19

theorem types_tail17 :
    Internal.vectorLoop funcType 49 { bytes := artifactBytes, pos := 80, limit := 534 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18

theorem types_tail16 :
    Internal.vectorLoop funcType 50 { bytes := artifactBytes, pos := 76, limit := 534 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17

theorem types_tail15 :
    Internal.vectorLoop funcType 51 { bytes := artifactBytes, pos := 72, limit := 534 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16

theorem types_tail14 :
    Internal.vectorLoop funcType 52 { bytes := artifactBytes, pos := 68, limit := 534 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15

theorem types_tail13 :
    Internal.vectorLoop funcType 53 { bytes := artifactBytes, pos := 64, limit := 534 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14

theorem types_tail12 :
    Internal.vectorLoop funcType 54 { bytes := artifactBytes, pos := 60, limit := 534 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 55 { bytes := artifactBytes, pos := 56, limit := 534 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 56 { bytes := artifactBytes, pos := 52, limit := 534 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 57 { bytes := artifactBytes, pos := 48, limit := 534 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 58 { bytes := artifactBytes, pos := 44, limit := 534 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 59 { bytes := artifactBytes, pos := 40, limit := 534 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 60 { bytes := artifactBytes, pos := 36, limit := 534 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 61 { bytes := artifactBytes, pos := 32, limit := 534 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 62 { bytes := artifactBytes, pos := 28, limit := 534 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 63 { bytes := artifactBytes, pos := 24, limit := 534 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 64 { bytes := artifactBytes, pos := 20, limit := 534 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 65 { bytes := artifactBytes, pos := 16, limit := 534 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 66 { bytes := artifactBytes, pos := 12, limit := 534 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 534 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 534, limit := 534 }) := by
  refine vector_eq_of_parts (length := 66)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 534 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 28315 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 534, limit := 28315 }) := by
  refine sized_eq_of_parts (size := 523)
    (payload := { bytes := artifactBytes, pos := 11, limit := 28315 }) (finish := { bytes := artifactBytes, pos := 534, limit := 534 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.Gpt2QuantizedCached.Artifact
