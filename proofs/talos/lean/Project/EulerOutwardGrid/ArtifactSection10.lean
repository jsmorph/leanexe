import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerOutwardGrid.ArtifactCode0
import Project.EulerOutwardGrid.ArtifactCode1
import Project.EulerOutwardGrid.ArtifactCode2
import Project.EulerOutwardGrid.ArtifactCode3
import Project.EulerOutwardGrid.ArtifactCode4
import Project.EulerOutwardGrid.ArtifactCode5
import Project.EulerOutwardGrid.ArtifactCode6
import Project.EulerOutwardGrid.ArtifactCode7
import Project.EulerOutwardGrid.ArtifactCode8
import Project.EulerOutwardGrid.ArtifactCode9
import Project.EulerOutwardGrid.ArtifactCode10
import Project.EulerOutwardGrid.ArtifactCode11
import Project.EulerOutwardGrid.ArtifactCode12
import Project.EulerOutwardGrid.ArtifactCode13
import Project.EulerOutwardGrid.ArtifactCode14
import Project.EulerOutwardGrid.ArtifactCode15
import Project.EulerOutwardGrid.ArtifactCode16
import Project.EulerOutwardGrid.ArtifactCode17
import Project.EulerOutwardGrid.ArtifactCode18
import Project.EulerOutwardGrid.ArtifactCode19
import Project.EulerOutwardGrid.ArtifactCode20
import Project.EulerOutwardGrid.ArtifactCode21
import Project.EulerOutwardGrid.ArtifactCode22
import Project.EulerOutwardGrid.ArtifactCode23
import Project.EulerOutwardGrid.ArtifactCode24
import Project.EulerOutwardGrid.ArtifactCode25
import Project.EulerOutwardGrid.ArtifactCode26
import Project.EulerOutwardGrid.ArtifactCode27
import Project.EulerOutwardGrid.ArtifactCode28
import Project.EulerOutwardGrid.ArtifactCode29
import Project.EulerOutwardGrid.ArtifactCode30
import Project.EulerOutwardGrid.ArtifactCode31
import Project.EulerOutwardGrid.ArtifactCode32
import Project.EulerOutwardGrid.ArtifactCode33
import Project.EulerOutwardGrid.ArtifactCode34
import Project.EulerOutwardGrid.ArtifactCode35
import Project.EulerOutwardGrid.ArtifactCode36
import Project.EulerOutwardGrid.ArtifactCode37
import Project.EulerOutwardGrid.ArtifactCode38
import Project.EulerOutwardGrid.ArtifactCode39
import Project.EulerOutwardGrid.ArtifactCode40
import Project.EulerOutwardGrid.ArtifactCode41
import Project.EulerOutwardGrid.ArtifactCode42
import Project.EulerOutwardGrid.ArtifactCode43
import Project.EulerOutwardGrid.ArtifactCode44
import Project.EulerOutwardGrid.ArtifactCode45
import Project.EulerOutwardGrid.ArtifactCode46
import Project.EulerOutwardGrid.ArtifactCode47
import Project.EulerOutwardGrid.ArtifactCode48
import Project.EulerOutwardGrid.ArtifactCode49

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail50 :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 5720, limit := 5720 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by rfl

theorem codes_tail49 :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 5367, limit := 5720 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50

theorem codes_tail48 :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 5286, limit := 5720 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49

theorem codes_tail47 :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 5258, limit := 5720 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48

theorem codes_tail46 :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 4891, limit := 5720 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47

theorem codes_tail45 :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 4565, limit := 5720 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46

theorem codes_tail44 :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 4488, limit := 5720 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45

theorem codes_tail43 :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 4459, limit := 5720 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44

theorem codes_tail42 :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 4352, limit := 5720 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43

theorem codes_tail41 :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 4341, limit := 5720 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42

theorem codes_tail40 :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 4330, limit := 5720 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41

theorem codes_tail39 :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 4319, limit := 5720 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40

theorem codes_tail38 :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 4308, limit := 5720 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39

theorem codes_tail37 :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 4042, limit := 5720 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38

theorem codes_tail36 :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 3923, limit := 5720 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37

theorem codes_tail35 :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 3812, limit := 5720 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36

theorem codes_tail34 :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 3600, limit := 5720 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35

theorem codes_tail33 :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 3466, limit := 5720 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34

theorem codes_tail32 :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 3347, limit := 5720 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33

theorem codes_tail31 :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 3235, limit := 5720 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32

theorem codes_tail30 :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 2884, limit := 5720 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31

theorem codes_tail29 :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 2772, limit := 5720 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30

theorem codes_tail28 :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 2660, limit := 5720 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29

theorem codes_tail27 :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 2530, limit := 5720 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28

theorem codes_tail26 :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 2403, limit := 5720 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27

theorem codes_tail25 :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 2347, limit := 5720 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26

theorem codes_tail24 :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 2278, limit := 5720 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25

theorem codes_tail23 :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 2209, limit := 5720 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24

theorem codes_tail22 :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 2126, limit := 5720 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23

theorem codes_tail21 :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 1795, limit := 5720 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22

theorem codes_tail20 :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 1659, limit := 5720 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21

theorem codes_tail19 :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 1591, limit := 5720 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20

theorem codes_tail18 :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 1475, limit := 5720 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19

theorem codes_tail17 :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 1400, limit := 5720 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18

theorem codes_tail16 :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 1341, limit := 5720 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17

theorem codes_tail15 :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 1309, limit := 5720 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16

theorem codes_tail14 :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 1227, limit := 5720 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15

theorem codes_tail13 :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 1128, limit := 5720 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14

theorem codes_tail12 :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 1082, limit := 5720 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13

theorem codes_tail11 :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 1060, limit := 5720 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12

theorem codes_tail10 :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 1023, limit := 5720 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11

theorem codes_tail9 :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 1000, limit := 5720 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10

theorem codes_tail8 :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 958, limit := 5720 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9

theorem codes_tail7 :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 830, limit := 5720 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8

theorem codes_tail6 :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 793, limit := 5720 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 770, limit := 5720 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 728, limit := 5720 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 619, limit := 5720 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 602, limit := 5720 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 591, limit := 5720 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 580, limit := 5720 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 579, limit := 5720 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  refine vector_eq_of_parts (length := 50)
    (itemsStart := { bytes := artifactBytes, pos := 580, limit := 5720 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 577, limit := 5720 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  refine sized_eq_of_parts (size := 5141)
    (payload := { bytes := artifactBytes, pos := 579, limit := 5720 }) (finish := { bytes := artifactBytes, pos := 5720, limit := 5720 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.EulerOutwardGrid.Artifact
