import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 12, limit := 342 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 16, limit := 342 }) := by cbv

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 16, limit := 342 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 20, limit := 342 }) := by cbv

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 20, limit := 342 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 24, limit := 342 }) := by cbv

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 24, limit := 342 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 28, limit := 342 }) := by cbv

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 28, limit := 342 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 32, limit := 342 }) := by cbv

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 32, limit := 342 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 36, limit := 342 }) := by cbv

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 36, limit := 342 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 40, limit := 342 }) := by cbv

theorem type7_decoded :
    funcType { bytes := artifactBytes, pos := 40, limit := 342 } =
      .ok (Cache.raw.types[7]!, { bytes := artifactBytes, pos := 44, limit := 342 }) := by cbv

theorem type8_decoded :
    funcType { bytes := artifactBytes, pos := 44, limit := 342 } =
      .ok (Cache.raw.types[8]!, { bytes := artifactBytes, pos := 48, limit := 342 }) := by cbv

theorem type9_decoded :
    funcType { bytes := artifactBytes, pos := 48, limit := 342 } =
      .ok (Cache.raw.types[9]!, { bytes := artifactBytes, pos := 52, limit := 342 }) := by cbv

theorem type10_decoded :
    funcType { bytes := artifactBytes, pos := 52, limit := 342 } =
      .ok (Cache.raw.types[10]!, { bytes := artifactBytes, pos := 56, limit := 342 }) := by cbv

theorem type11_decoded :
    funcType { bytes := artifactBytes, pos := 56, limit := 342 } =
      .ok (Cache.raw.types[11]!, { bytes := artifactBytes, pos := 60, limit := 342 }) := by cbv

theorem type12_decoded :
    funcType { bytes := artifactBytes, pos := 60, limit := 342 } =
      .ok (Cache.raw.types[12]!, { bytes := artifactBytes, pos := 64, limit := 342 }) := by cbv

theorem type13_decoded :
    funcType { bytes := artifactBytes, pos := 64, limit := 342 } =
      .ok (Cache.raw.types[13]!, { bytes := artifactBytes, pos := 68, limit := 342 }) := by cbv

theorem type14_decoded :
    funcType { bytes := artifactBytes, pos := 68, limit := 342 } =
      .ok (Cache.raw.types[14]!, { bytes := artifactBytes, pos := 72, limit := 342 }) := by cbv

theorem type15_decoded :
    funcType { bytes := artifactBytes, pos := 72, limit := 342 } =
      .ok (Cache.raw.types[15]!, { bytes := artifactBytes, pos := 76, limit := 342 }) := by cbv

theorem type16_decoded :
    funcType { bytes := artifactBytes, pos := 76, limit := 342 } =
      .ok (Cache.raw.types[16]!, { bytes := artifactBytes, pos := 80, limit := 342 }) := by cbv

theorem type17_decoded :
    funcType { bytes := artifactBytes, pos := 80, limit := 342 } =
      .ok (Cache.raw.types[17]!, { bytes := artifactBytes, pos := 88, limit := 342 }) := by cbv

theorem type18_decoded :
    funcType { bytes := artifactBytes, pos := 88, limit := 342 } =
      .ok (Cache.raw.types[18]!, { bytes := artifactBytes, pos := 96, limit := 342 }) := by cbv

theorem type19_decoded :
    funcType { bytes := artifactBytes, pos := 96, limit := 342 } =
      .ok (Cache.raw.types[19]!, { bytes := artifactBytes, pos := 105, limit := 342 }) := by cbv

theorem type20_decoded :
    funcType { bytes := artifactBytes, pos := 105, limit := 342 } =
      .ok (Cache.raw.types[20]!, { bytes := artifactBytes, pos := 120, limit := 342 }) := by cbv

theorem type21_decoded :
    funcType { bytes := artifactBytes, pos := 120, limit := 342 } =
      .ok (Cache.raw.types[21]!, { bytes := artifactBytes, pos := 137, limit := 342 }) := by cbv

theorem type22_decoded :
    funcType { bytes := artifactBytes, pos := 137, limit := 342 } =
      .ok (Cache.raw.types[22]!, { bytes := artifactBytes, pos := 151, limit := 342 }) := by cbv

theorem type23_decoded :
    funcType { bytes := artifactBytes, pos := 151, limit := 342 } =
      .ok (Cache.raw.types[23]!, { bytes := artifactBytes, pos := 165, limit := 342 }) := by cbv

theorem type24_decoded :
    funcType { bytes := artifactBytes, pos := 165, limit := 342 } =
      .ok (Cache.raw.types[24]!, { bytes := artifactBytes, pos := 171, limit := 342 }) := by cbv

theorem type25_decoded :
    funcType { bytes := artifactBytes, pos := 171, limit := 342 } =
      .ok (Cache.raw.types[25]!, { bytes := artifactBytes, pos := 180, limit := 342 }) := by cbv

theorem type26_decoded :
    funcType { bytes := artifactBytes, pos := 180, limit := 342 } =
      .ok (Cache.raw.types[26]!, { bytes := artifactBytes, pos := 185, limit := 342 }) := by cbv

theorem type27_decoded :
    funcType { bytes := artifactBytes, pos := 185, limit := 342 } =
      .ok (Cache.raw.types[27]!, { bytes := artifactBytes, pos := 190, limit := 342 }) := by cbv

theorem type28_decoded :
    funcType { bytes := artifactBytes, pos := 190, limit := 342 } =
      .ok (Cache.raw.types[28]!, { bytes := artifactBytes, pos := 199, limit := 342 }) := by cbv

theorem type29_decoded :
    funcType { bytes := artifactBytes, pos := 199, limit := 342 } =
      .ok (Cache.raw.types[29]!, { bytes := artifactBytes, pos := 213, limit := 342 }) := by cbv

theorem type30_decoded :
    funcType { bytes := artifactBytes, pos := 213, limit := 342 } =
      .ok (Cache.raw.types[30]!, { bytes := artifactBytes, pos := 225, limit := 342 }) := by cbv

theorem type31_decoded :
    funcType { bytes := artifactBytes, pos := 225, limit := 342 } =
      .ok (Cache.raw.types[31]!, { bytes := artifactBytes, pos := 230, limit := 342 }) := by cbv

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 230, limit := 342 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 239, limit := 342 }) := by cbv

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 239, limit := 342 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 259, limit := 342 }) := by cbv

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 259, limit := 342 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 271, limit := 342 }) := by cbv

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 271, limit := 342 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 283, limit := 342 }) := by cbv

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 283, limit := 342 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 300, limit := 342 }) := by cbv

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 300, limit := 342 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 312, limit := 342 }) := by cbv

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 312, limit := 342 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 325, limit := 342 }) := by cbv

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 325, limit := 342 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 330, limit := 342 }) := by cbv

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 330, limit := 342 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 333, limit := 342 }) := by cbv

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 333, limit := 342 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 338, limit := 342 }) := by cbv

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 338, limit := 342 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 342, limit := 342 }) := by cbv

theorem types_tail43 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 342, limit := 342 } =
      .ok (Cache.raw.types.drop 43, { bytes := artifactBytes, pos := 342, limit := 342 }) := by rfl

theorem types_tail42 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 338, limit := 342 } =
      .ok (Cache.raw.types.drop 42, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type42_decoded types_tail43

theorem types_tail41 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 333, limit := 342 } =
      .ok (Cache.raw.types.drop 41, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type41_decoded types_tail42

theorem types_tail40 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 330, limit := 342 } =
      .ok (Cache.raw.types.drop 40, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type40_decoded types_tail41

theorem types_tail39 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 325, limit := 342 } =
      .ok (Cache.raw.types.drop 39, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type39_decoded types_tail40

theorem types_tail38 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 312, limit := 342 } =
      .ok (Cache.raw.types.drop 38, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type38_decoded types_tail39

theorem types_tail37 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 300, limit := 342 } =
      .ok (Cache.raw.types.drop 37, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type37_decoded types_tail38

theorem types_tail36 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 283, limit := 342 } =
      .ok (Cache.raw.types.drop 36, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type36_decoded types_tail37

theorem types_tail35 :
    Internal.vectorLoop funcType 8 { bytes := artifactBytes, pos := 271, limit := 342 } =
      .ok (Cache.raw.types.drop 35, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type35_decoded types_tail36

theorem types_tail34 :
    Internal.vectorLoop funcType 9 { bytes := artifactBytes, pos := 259, limit := 342 } =
      .ok (Cache.raw.types.drop 34, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type34_decoded types_tail35

theorem types_tail33 :
    Internal.vectorLoop funcType 10 { bytes := artifactBytes, pos := 239, limit := 342 } =
      .ok (Cache.raw.types.drop 33, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type33_decoded types_tail34

theorem types_tail32 :
    Internal.vectorLoop funcType 11 { bytes := artifactBytes, pos := 230, limit := 342 } =
      .ok (Cache.raw.types.drop 32, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type32_decoded types_tail33

theorem types_tail31 :
    Internal.vectorLoop funcType 12 { bytes := artifactBytes, pos := 225, limit := 342 } =
      .ok (Cache.raw.types.drop 31, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type31_decoded types_tail32

theorem types_tail30 :
    Internal.vectorLoop funcType 13 { bytes := artifactBytes, pos := 213, limit := 342 } =
      .ok (Cache.raw.types.drop 30, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type30_decoded types_tail31

theorem types_tail29 :
    Internal.vectorLoop funcType 14 { bytes := artifactBytes, pos := 199, limit := 342 } =
      .ok (Cache.raw.types.drop 29, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type29_decoded types_tail30

theorem types_tail28 :
    Internal.vectorLoop funcType 15 { bytes := artifactBytes, pos := 190, limit := 342 } =
      .ok (Cache.raw.types.drop 28, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type28_decoded types_tail29

theorem types_tail27 :
    Internal.vectorLoop funcType 16 { bytes := artifactBytes, pos := 185, limit := 342 } =
      .ok (Cache.raw.types.drop 27, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type27_decoded types_tail28

theorem types_tail26 :
    Internal.vectorLoop funcType 17 { bytes := artifactBytes, pos := 180, limit := 342 } =
      .ok (Cache.raw.types.drop 26, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type26_decoded types_tail27

theorem types_tail25 :
    Internal.vectorLoop funcType 18 { bytes := artifactBytes, pos := 171, limit := 342 } =
      .ok (Cache.raw.types.drop 25, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type25_decoded types_tail26

theorem types_tail24 :
    Internal.vectorLoop funcType 19 { bytes := artifactBytes, pos := 165, limit := 342 } =
      .ok (Cache.raw.types.drop 24, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type24_decoded types_tail25

theorem types_tail23 :
    Internal.vectorLoop funcType 20 { bytes := artifactBytes, pos := 151, limit := 342 } =
      .ok (Cache.raw.types.drop 23, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type23_decoded types_tail24

theorem types_tail22 :
    Internal.vectorLoop funcType 21 { bytes := artifactBytes, pos := 137, limit := 342 } =
      .ok (Cache.raw.types.drop 22, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type22_decoded types_tail23

theorem types_tail21 :
    Internal.vectorLoop funcType 22 { bytes := artifactBytes, pos := 120, limit := 342 } =
      .ok (Cache.raw.types.drop 21, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type21_decoded types_tail22

theorem types_tail20 :
    Internal.vectorLoop funcType 23 { bytes := artifactBytes, pos := 105, limit := 342 } =
      .ok (Cache.raw.types.drop 20, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type20_decoded types_tail21

theorem types_tail19 :
    Internal.vectorLoop funcType 24 { bytes := artifactBytes, pos := 96, limit := 342 } =
      .ok (Cache.raw.types.drop 19, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type19_decoded types_tail20

theorem types_tail18 :
    Internal.vectorLoop funcType 25 { bytes := artifactBytes, pos := 88, limit := 342 } =
      .ok (Cache.raw.types.drop 18, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type18_decoded types_tail19

theorem types_tail17 :
    Internal.vectorLoop funcType 26 { bytes := artifactBytes, pos := 80, limit := 342 } =
      .ok (Cache.raw.types.drop 17, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type17_decoded types_tail18

theorem types_tail16 :
    Internal.vectorLoop funcType 27 { bytes := artifactBytes, pos := 76, limit := 342 } =
      .ok (Cache.raw.types.drop 16, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type16_decoded types_tail17

theorem types_tail15 :
    Internal.vectorLoop funcType 28 { bytes := artifactBytes, pos := 72, limit := 342 } =
      .ok (Cache.raw.types.drop 15, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type15_decoded types_tail16

theorem types_tail14 :
    Internal.vectorLoop funcType 29 { bytes := artifactBytes, pos := 68, limit := 342 } =
      .ok (Cache.raw.types.drop 14, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type14_decoded types_tail15

theorem types_tail13 :
    Internal.vectorLoop funcType 30 { bytes := artifactBytes, pos := 64, limit := 342 } =
      .ok (Cache.raw.types.drop 13, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type13_decoded types_tail14

theorem types_tail12 :
    Internal.vectorLoop funcType 31 { bytes := artifactBytes, pos := 60, limit := 342 } =
      .ok (Cache.raw.types.drop 12, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type12_decoded types_tail13

theorem types_tail11 :
    Internal.vectorLoop funcType 32 { bytes := artifactBytes, pos := 56, limit := 342 } =
      .ok (Cache.raw.types.drop 11, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type11_decoded types_tail12

theorem types_tail10 :
    Internal.vectorLoop funcType 33 { bytes := artifactBytes, pos := 52, limit := 342 } =
      .ok (Cache.raw.types.drop 10, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type10_decoded types_tail11

theorem types_tail9 :
    Internal.vectorLoop funcType 34 { bytes := artifactBytes, pos := 48, limit := 342 } =
      .ok (Cache.raw.types.drop 9, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type9_decoded types_tail10

theorem types_tail8 :
    Internal.vectorLoop funcType 35 { bytes := artifactBytes, pos := 44, limit := 342 } =
      .ok (Cache.raw.types.drop 8, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type8_decoded types_tail9

theorem types_tail7 :
    Internal.vectorLoop funcType 36 { bytes := artifactBytes, pos := 40, limit := 342 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type7_decoded types_tail8

theorem types_tail6 :
    Internal.vectorLoop funcType 37 { bytes := artifactBytes, pos := 36, limit := 342 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 38 { bytes := artifactBytes, pos := 32, limit := 342 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 39 { bytes := artifactBytes, pos := 28, limit := 342 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 40 { bytes := artifactBytes, pos := 24, limit := 342 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 41 { bytes := artifactBytes, pos := 20, limit := 342 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 42 { bytes := artifactBytes, pos := 16, limit := 342 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 43 { bytes := artifactBytes, pos := 12, limit := 342 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 11, limit := 342 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  refine vector_eq_of_parts (length := 43)
    (itemsStart := { bytes := artifactBytes, pos := 12, limit := 342 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 19083 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 342, limit := 19083 }) := by
  refine sized_eq_of_parts (size := 331)
    (payload := { bytes := artifactBytes, pos := 11, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 342, limit := 342 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.Gpt2CachedStep.Artifact
