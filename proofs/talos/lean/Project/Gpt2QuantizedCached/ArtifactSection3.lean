import Project.Gpt2QuantizedCached.ArtifactSection3Items0
import Project.Gpt2QuantizedCached.ArtifactSection3Items1
import Project.Gpt2QuantizedCached.ArtifactSection3Items2
import Project.Gpt2QuantizedCached.ArtifactSection3Items3
import Project.Gpt2QuantizedCached.ArtifactSection3Items4
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionTypeIndices_tail66 :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 603, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 66, { bytes := artifactBytes, pos := 603, limit := 603 }) := by rfl

theorem functionTypeIndices_tail65 :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 602, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 65, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function65_decoded functionTypeIndices_tail66

theorem functionTypeIndices_tail64 :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 601, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 64, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function64_decoded functionTypeIndices_tail65

theorem functionTypeIndices_tail63 :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 600, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 63, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function63_decoded functionTypeIndices_tail64

theorem functionTypeIndices_tail62 :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 599, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 62, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function62_decoded functionTypeIndices_tail63

theorem functionTypeIndices_tail61 :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 598, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 61, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function61_decoded functionTypeIndices_tail62

theorem functionTypeIndices_tail60 :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 597, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 60, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function60_decoded functionTypeIndices_tail61

theorem functionTypeIndices_tail59 :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 596, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 59, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function59_decoded functionTypeIndices_tail60

theorem functionTypeIndices_tail58 :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 595, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 58, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function58_decoded functionTypeIndices_tail59

theorem functionTypeIndices_tail57 :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 594, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 57, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function57_decoded functionTypeIndices_tail58

theorem functionTypeIndices_tail56 :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 593, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 56, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function56_decoded functionTypeIndices_tail57

theorem functionTypeIndices_tail55 :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 592, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 55, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function55_decoded functionTypeIndices_tail56

theorem functionTypeIndices_tail54 :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 591, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 54, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function54_decoded functionTypeIndices_tail55

theorem functionTypeIndices_tail53 :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 590, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 53, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function53_decoded functionTypeIndices_tail54

theorem functionTypeIndices_tail52 :
    Internal.vectorLoop Leb.u32 14 { bytes := artifactBytes, pos := 589, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 52, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function52_decoded functionTypeIndices_tail53

theorem functionTypeIndices_tail51 :
    Internal.vectorLoop Leb.u32 15 { bytes := artifactBytes, pos := 588, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 51, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function51_decoded functionTypeIndices_tail52

theorem functionTypeIndices_tail50 :
    Internal.vectorLoop Leb.u32 16 { bytes := artifactBytes, pos := 587, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 50, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function50_decoded functionTypeIndices_tail51

theorem functionTypeIndices_tail49 :
    Internal.vectorLoop Leb.u32 17 { bytes := artifactBytes, pos := 586, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 49, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function49_decoded functionTypeIndices_tail50

theorem functionTypeIndices_tail48 :
    Internal.vectorLoop Leb.u32 18 { bytes := artifactBytes, pos := 585, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 48, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function48_decoded functionTypeIndices_tail49

theorem functionTypeIndices_tail47 :
    Internal.vectorLoop Leb.u32 19 { bytes := artifactBytes, pos := 584, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 47, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function47_decoded functionTypeIndices_tail48

theorem functionTypeIndices_tail46 :
    Internal.vectorLoop Leb.u32 20 { bytes := artifactBytes, pos := 583, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 46, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function46_decoded functionTypeIndices_tail47

theorem functionTypeIndices_tail45 :
    Internal.vectorLoop Leb.u32 21 { bytes := artifactBytes, pos := 582, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 45, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function45_decoded functionTypeIndices_tail46

theorem functionTypeIndices_tail44 :
    Internal.vectorLoop Leb.u32 22 { bytes := artifactBytes, pos := 581, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 44, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function44_decoded functionTypeIndices_tail45

theorem functionTypeIndices_tail43 :
    Internal.vectorLoop Leb.u32 23 { bytes := artifactBytes, pos := 580, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function43_decoded functionTypeIndices_tail44

theorem functionTypeIndices_tail42 :
    Internal.vectorLoop Leb.u32 24 { bytes := artifactBytes, pos := 579, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function42_decoded functionTypeIndices_tail43

theorem functionTypeIndices_tail41 :
    Internal.vectorLoop Leb.u32 25 { bytes := artifactBytes, pos := 578, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function41_decoded functionTypeIndices_tail42

theorem functionTypeIndices_tail40 :
    Internal.vectorLoop Leb.u32 26 { bytes := artifactBytes, pos := 577, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function40_decoded functionTypeIndices_tail41

theorem functionTypeIndices_tail39 :
    Internal.vectorLoop Leb.u32 27 { bytes := artifactBytes, pos := 576, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function39_decoded functionTypeIndices_tail40

theorem functionTypeIndices_tail38 :
    Internal.vectorLoop Leb.u32 28 { bytes := artifactBytes, pos := 575, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function38_decoded functionTypeIndices_tail39

theorem functionTypeIndices_tail37 :
    Internal.vectorLoop Leb.u32 29 { bytes := artifactBytes, pos := 574, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function37_decoded functionTypeIndices_tail38

theorem functionTypeIndices_tail36 :
    Internal.vectorLoop Leb.u32 30 { bytes := artifactBytes, pos := 573, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function36_decoded functionTypeIndices_tail37

theorem functionTypeIndices_tail35 :
    Internal.vectorLoop Leb.u32 31 { bytes := artifactBytes, pos := 572, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function35_decoded functionTypeIndices_tail36

theorem functionTypeIndices_tail34 :
    Internal.vectorLoop Leb.u32 32 { bytes := artifactBytes, pos := 571, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function34_decoded functionTypeIndices_tail35

theorem functionTypeIndices_tail33 :
    Internal.vectorLoop Leb.u32 33 { bytes := artifactBytes, pos := 570, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function33_decoded functionTypeIndices_tail34

theorem functionTypeIndices_tail32 :
    Internal.vectorLoop Leb.u32 34 { bytes := artifactBytes, pos := 569, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function32_decoded functionTypeIndices_tail33

theorem functionTypeIndices_tail31 :
    Internal.vectorLoop Leb.u32 35 { bytes := artifactBytes, pos := 568, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function31_decoded functionTypeIndices_tail32

theorem functionTypeIndices_tail30 :
    Internal.vectorLoop Leb.u32 36 { bytes := artifactBytes, pos := 567, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function30_decoded functionTypeIndices_tail31

theorem functionTypeIndices_tail29 :
    Internal.vectorLoop Leb.u32 37 { bytes := artifactBytes, pos := 566, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function29_decoded functionTypeIndices_tail30

theorem functionTypeIndices_tail28 :
    Internal.vectorLoop Leb.u32 38 { bytes := artifactBytes, pos := 565, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function28_decoded functionTypeIndices_tail29

theorem functionTypeIndices_tail27 :
    Internal.vectorLoop Leb.u32 39 { bytes := artifactBytes, pos := 564, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function27_decoded functionTypeIndices_tail28

theorem functionTypeIndices_tail26 :
    Internal.vectorLoop Leb.u32 40 { bytes := artifactBytes, pos := 563, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function26_decoded functionTypeIndices_tail27

theorem functionTypeIndices_tail25 :
    Internal.vectorLoop Leb.u32 41 { bytes := artifactBytes, pos := 562, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function25_decoded functionTypeIndices_tail26

theorem functionTypeIndices_tail24 :
    Internal.vectorLoop Leb.u32 42 { bytes := artifactBytes, pos := 561, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function24_decoded functionTypeIndices_tail25

theorem functionTypeIndices_tail23 :
    Internal.vectorLoop Leb.u32 43 { bytes := artifactBytes, pos := 560, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function23_decoded functionTypeIndices_tail24

theorem functionTypeIndices_tail22 :
    Internal.vectorLoop Leb.u32 44 { bytes := artifactBytes, pos := 559, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function22_decoded functionTypeIndices_tail23

theorem functionTypeIndices_tail21 :
    Internal.vectorLoop Leb.u32 45 { bytes := artifactBytes, pos := 558, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function21_decoded functionTypeIndices_tail22

theorem functionTypeIndices_tail20 :
    Internal.vectorLoop Leb.u32 46 { bytes := artifactBytes, pos := 557, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function20_decoded functionTypeIndices_tail21

theorem functionTypeIndices_tail19 :
    Internal.vectorLoop Leb.u32 47 { bytes := artifactBytes, pos := 556, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function19_decoded functionTypeIndices_tail20

theorem functionTypeIndices_tail18 :
    Internal.vectorLoop Leb.u32 48 { bytes := artifactBytes, pos := 555, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function18_decoded functionTypeIndices_tail19

theorem functionTypeIndices_tail17 :
    Internal.vectorLoop Leb.u32 49 { bytes := artifactBytes, pos := 554, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function17_decoded functionTypeIndices_tail18

theorem functionTypeIndices_tail16 :
    Internal.vectorLoop Leb.u32 50 { bytes := artifactBytes, pos := 553, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function16_decoded functionTypeIndices_tail17

theorem functionTypeIndices_tail15 :
    Internal.vectorLoop Leb.u32 51 { bytes := artifactBytes, pos := 552, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function15_decoded functionTypeIndices_tail16

theorem functionTypeIndices_tail14 :
    Internal.vectorLoop Leb.u32 52 { bytes := artifactBytes, pos := 551, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function14_decoded functionTypeIndices_tail15

theorem functionTypeIndices_tail13 :
    Internal.vectorLoop Leb.u32 53 { bytes := artifactBytes, pos := 550, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function13_decoded functionTypeIndices_tail14

theorem functionTypeIndices_tail12 :
    Internal.vectorLoop Leb.u32 54 { bytes := artifactBytes, pos := 549, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function12_decoded functionTypeIndices_tail13

theorem functionTypeIndices_tail11 :
    Internal.vectorLoop Leb.u32 55 { bytes := artifactBytes, pos := 548, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function11_decoded functionTypeIndices_tail12

theorem functionTypeIndices_tail10 :
    Internal.vectorLoop Leb.u32 56 { bytes := artifactBytes, pos := 547, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function10_decoded functionTypeIndices_tail11

theorem functionTypeIndices_tail9 :
    Internal.vectorLoop Leb.u32 57 { bytes := artifactBytes, pos := 546, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function9_decoded functionTypeIndices_tail10

theorem functionTypeIndices_tail8 :
    Internal.vectorLoop Leb.u32 58 { bytes := artifactBytes, pos := 545, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function8_decoded functionTypeIndices_tail9

theorem functionTypeIndices_tail7 :
    Internal.vectorLoop Leb.u32 59 { bytes := artifactBytes, pos := 544, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function7_decoded functionTypeIndices_tail8

theorem functionTypeIndices_tail6 :
    Internal.vectorLoop Leb.u32 60 { bytes := artifactBytes, pos := 543, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function6_decoded functionTypeIndices_tail7

theorem functionTypeIndices_tail5 :
    Internal.vectorLoop Leb.u32 61 { bytes := artifactBytes, pos := 542, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function5_decoded functionTypeIndices_tail6

theorem functionTypeIndices_tail4 :
    Internal.vectorLoop Leb.u32 62 { bytes := artifactBytes, pos := 541, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function4_decoded functionTypeIndices_tail5

theorem functionTypeIndices_tail3 :
    Internal.vectorLoop Leb.u32 63 { bytes := artifactBytes, pos := 540, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function3_decoded functionTypeIndices_tail4

theorem functionTypeIndices_tail2 :
    Internal.vectorLoop Leb.u32 64 { bytes := artifactBytes, pos := 539, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function2_decoded functionTypeIndices_tail3

theorem functionTypeIndices_tail1 :
    Internal.vectorLoop Leb.u32 65 { bytes := artifactBytes, pos := 538, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function1_decoded functionTypeIndices_tail2

theorem functionTypeIndices_tail0 :
    Internal.vectorLoop Leb.u32 66 { bytes := artifactBytes, pos := 537, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  exact vectorLoop_eq_cons function0_decoded functionTypeIndices_tail1

theorem functionTypeIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 536, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 603, limit := 603 }) := by
  refine vector_eq_of_parts (length := 66)
    (itemsStart := { bytes := artifactBytes, pos := 537, limit := 603 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 535, limit := 28315 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 603, limit := 28315 }) := by
  refine sized_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 536, limit := 28315 }) (finish := { bytes := artifactBytes, pos := 603, limit := 603 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.Gpt2QuantizedCached.Artifact
