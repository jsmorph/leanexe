import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function0_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 345, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 346, limit := 388 }) := by cbv

theorem function1_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 346, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 347, limit := 388 }) := by cbv

theorem function2_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 347, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 348, limit := 388 }) := by cbv

theorem function3_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 348, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 349, limit := 388 }) := by cbv

theorem function4_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 349, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 350, limit := 388 }) := by cbv

theorem function5_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 350, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 351, limit := 388 }) := by cbv

theorem function6_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 351, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 352, limit := 388 }) := by cbv

theorem function7_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 352, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 353, limit := 388 }) := by cbv

theorem function8_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 353, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 354, limit := 388 }) := by cbv

theorem function9_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 354, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 355, limit := 388 }) := by cbv

theorem function10_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 355, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 356, limit := 388 }) := by cbv

theorem function11_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 356, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 357, limit := 388 }) := by cbv

theorem function12_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 357, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 358, limit := 388 }) := by cbv

theorem function13_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 358, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 359, limit := 388 }) := by cbv

theorem function14_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 359, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 360, limit := 388 }) := by cbv

theorem function15_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 360, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 361, limit := 388 }) := by cbv

theorem function16_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 361, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 362, limit := 388 }) := by cbv

theorem function17_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 362, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 363, limit := 388 }) := by cbv

theorem function18_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 363, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 364, limit := 388 }) := by cbv

theorem function19_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 364, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 365, limit := 388 }) := by cbv

theorem function20_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 365, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 366, limit := 388 }) := by cbv

theorem function21_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 366, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 367, limit := 388 }) := by cbv

theorem function22_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 367, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 368, limit := 388 }) := by cbv

theorem function23_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 368, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 369, limit := 388 }) := by cbv

theorem function24_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 369, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 370, limit := 388 }) := by cbv

theorem function25_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 370, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 371, limit := 388 }) := by cbv

theorem function26_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 371, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 372, limit := 388 }) := by cbv

theorem function27_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 372, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 373, limit := 388 }) := by cbv

theorem function28_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 373, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 374, limit := 388 }) := by cbv

theorem function29_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 374, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 375, limit := 388 }) := by cbv

theorem function30_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 375, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 376, limit := 388 }) := by cbv

theorem function31_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 376, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 377, limit := 388 }) := by cbv

theorem function32_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 377, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 378, limit := 388 }) := by cbv

theorem function33_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 378, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 379, limit := 388 }) := by cbv

theorem function34_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 379, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 380, limit := 388 }) := by cbv

theorem function35_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 380, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 381, limit := 388 }) := by cbv

theorem function36_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 381, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 382, limit := 388 }) := by cbv

theorem function37_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 382, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 383, limit := 388 }) := by cbv

theorem function38_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 383, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 384, limit := 388 }) := by cbv

theorem function39_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 384, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 385, limit := 388 }) := by cbv

theorem function40_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 385, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 386, limit := 388 }) := by cbv

theorem function41_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 386, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 387, limit := 388 }) := by cbv

theorem function42_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 387, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 388, limit := 388 }) := by cbv

theorem functionTypeIndices_tail43 :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 388, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 388, limit := 388 }) := by rfl

theorem functionTypeIndices_tail42 :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 387, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function42_decoded functionTypeIndices_tail43

theorem functionTypeIndices_tail41 :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 386, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function41_decoded functionTypeIndices_tail42

theorem functionTypeIndices_tail40 :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 385, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function40_decoded functionTypeIndices_tail41

theorem functionTypeIndices_tail39 :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 384, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function39_decoded functionTypeIndices_tail40

theorem functionTypeIndices_tail38 :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 383, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function38_decoded functionTypeIndices_tail39

theorem functionTypeIndices_tail37 :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 382, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function37_decoded functionTypeIndices_tail38

theorem functionTypeIndices_tail36 :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 381, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function36_decoded functionTypeIndices_tail37

theorem functionTypeIndices_tail35 :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 380, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function35_decoded functionTypeIndices_tail36

theorem functionTypeIndices_tail34 :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 379, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function34_decoded functionTypeIndices_tail35

theorem functionTypeIndices_tail33 :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 378, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function33_decoded functionTypeIndices_tail34

theorem functionTypeIndices_tail32 :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 377, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function32_decoded functionTypeIndices_tail33

theorem functionTypeIndices_tail31 :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 376, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function31_decoded functionTypeIndices_tail32

theorem functionTypeIndices_tail30 :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 375, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function30_decoded functionTypeIndices_tail31

theorem functionTypeIndices_tail29 :
    Internal.vectorLoop Leb.u32 14 { bytes := artifactBytes, pos := 374, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function29_decoded functionTypeIndices_tail30

theorem functionTypeIndices_tail28 :
    Internal.vectorLoop Leb.u32 15 { bytes := artifactBytes, pos := 373, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function28_decoded functionTypeIndices_tail29

theorem functionTypeIndices_tail27 :
    Internal.vectorLoop Leb.u32 16 { bytes := artifactBytes, pos := 372, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function27_decoded functionTypeIndices_tail28

theorem functionTypeIndices_tail26 :
    Internal.vectorLoop Leb.u32 17 { bytes := artifactBytes, pos := 371, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function26_decoded functionTypeIndices_tail27

theorem functionTypeIndices_tail25 :
    Internal.vectorLoop Leb.u32 18 { bytes := artifactBytes, pos := 370, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function25_decoded functionTypeIndices_tail26

theorem functionTypeIndices_tail24 :
    Internal.vectorLoop Leb.u32 19 { bytes := artifactBytes, pos := 369, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function24_decoded functionTypeIndices_tail25

theorem functionTypeIndices_tail23 :
    Internal.vectorLoop Leb.u32 20 { bytes := artifactBytes, pos := 368, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function23_decoded functionTypeIndices_tail24

theorem functionTypeIndices_tail22 :
    Internal.vectorLoop Leb.u32 21 { bytes := artifactBytes, pos := 367, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function22_decoded functionTypeIndices_tail23

theorem functionTypeIndices_tail21 :
    Internal.vectorLoop Leb.u32 22 { bytes := artifactBytes, pos := 366, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function21_decoded functionTypeIndices_tail22

theorem functionTypeIndices_tail20 :
    Internal.vectorLoop Leb.u32 23 { bytes := artifactBytes, pos := 365, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function20_decoded functionTypeIndices_tail21

theorem functionTypeIndices_tail19 :
    Internal.vectorLoop Leb.u32 24 { bytes := artifactBytes, pos := 364, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function19_decoded functionTypeIndices_tail20

theorem functionTypeIndices_tail18 :
    Internal.vectorLoop Leb.u32 25 { bytes := artifactBytes, pos := 363, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function18_decoded functionTypeIndices_tail19

theorem functionTypeIndices_tail17 :
    Internal.vectorLoop Leb.u32 26 { bytes := artifactBytes, pos := 362, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function17_decoded functionTypeIndices_tail18

theorem functionTypeIndices_tail16 :
    Internal.vectorLoop Leb.u32 27 { bytes := artifactBytes, pos := 361, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function16_decoded functionTypeIndices_tail17

theorem functionTypeIndices_tail15 :
    Internal.vectorLoop Leb.u32 28 { bytes := artifactBytes, pos := 360, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function15_decoded functionTypeIndices_tail16

theorem functionTypeIndices_tail14 :
    Internal.vectorLoop Leb.u32 29 { bytes := artifactBytes, pos := 359, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function14_decoded functionTypeIndices_tail15

theorem functionTypeIndices_tail13 :
    Internal.vectorLoop Leb.u32 30 { bytes := artifactBytes, pos := 358, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function13_decoded functionTypeIndices_tail14

theorem functionTypeIndices_tail12 :
    Internal.vectorLoop Leb.u32 31 { bytes := artifactBytes, pos := 357, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function12_decoded functionTypeIndices_tail13

theorem functionTypeIndices_tail11 :
    Internal.vectorLoop Leb.u32 32 { bytes := artifactBytes, pos := 356, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function11_decoded functionTypeIndices_tail12

theorem functionTypeIndices_tail10 :
    Internal.vectorLoop Leb.u32 33 { bytes := artifactBytes, pos := 355, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function10_decoded functionTypeIndices_tail11

theorem functionTypeIndices_tail9 :
    Internal.vectorLoop Leb.u32 34 { bytes := artifactBytes, pos := 354, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function9_decoded functionTypeIndices_tail10

theorem functionTypeIndices_tail8 :
    Internal.vectorLoop Leb.u32 35 { bytes := artifactBytes, pos := 353, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function8_decoded functionTypeIndices_tail9

theorem functionTypeIndices_tail7 :
    Internal.vectorLoop Leb.u32 36 { bytes := artifactBytes, pos := 352, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function7_decoded functionTypeIndices_tail8

theorem functionTypeIndices_tail6 :
    Internal.vectorLoop Leb.u32 37 { bytes := artifactBytes, pos := 351, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function6_decoded functionTypeIndices_tail7

theorem functionTypeIndices_tail5 :
    Internal.vectorLoop Leb.u32 38 { bytes := artifactBytes, pos := 350, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function5_decoded functionTypeIndices_tail6

theorem functionTypeIndices_tail4 :
    Internal.vectorLoop Leb.u32 39 { bytes := artifactBytes, pos := 349, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function4_decoded functionTypeIndices_tail5

theorem functionTypeIndices_tail3 :
    Internal.vectorLoop Leb.u32 40 { bytes := artifactBytes, pos := 348, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function3_decoded functionTypeIndices_tail4

theorem functionTypeIndices_tail2 :
    Internal.vectorLoop Leb.u32 41 { bytes := artifactBytes, pos := 347, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function2_decoded functionTypeIndices_tail3

theorem functionTypeIndices_tail1 :
    Internal.vectorLoop Leb.u32 42 { bytes := artifactBytes, pos := 346, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function1_decoded functionTypeIndices_tail2

theorem functionTypeIndices_tail0 :
    Internal.vectorLoop Leb.u32 43 { bytes := artifactBytes, pos := 345, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  exact vectorLoop_eq_cons function0_decoded functionTypeIndices_tail1

theorem functionTypeIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 344, limit := 388 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 388, limit := 388 }) := by
  refine vector_eq_of_parts (length := 43)
    (itemsStart := { bytes := artifactBytes, pos := 345, limit := 388 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 343, limit := 19083 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 388, limit := 19083 }) := by
  refine sized_eq_of_parts (size := 44)
    (payload := { bytes := artifactBytes, pos := 344, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 388, limit := 388 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.Gpt2CachedStep.Artifact
