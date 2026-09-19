import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2CachedStep.ArtifactCode0
import Project.Gpt2CachedStep.ArtifactCode1
import Project.Gpt2CachedStep.ArtifactCode2
import Project.Gpt2CachedStep.ArtifactCode3
import Project.Gpt2CachedStep.ArtifactCode4
import Project.Gpt2CachedStep.ArtifactCode5
import Project.Gpt2CachedStep.ArtifactCode6
import Project.Gpt2CachedStep.ArtifactCode7
import Project.Gpt2CachedStep.ArtifactCode8
import Project.Gpt2CachedStep.ArtifactCode9
import Project.Gpt2CachedStep.ArtifactCode10
import Project.Gpt2CachedStep.ArtifactCode11
import Project.Gpt2CachedStep.ArtifactCode12
import Project.Gpt2CachedStep.ArtifactCode13
import Project.Gpt2CachedStep.ArtifactCode14
import Project.Gpt2CachedStep.ArtifactCode15
import Project.Gpt2CachedStep.ArtifactCode16
import Project.Gpt2CachedStep.ArtifactCode17
import Project.Gpt2CachedStep.ArtifactCode18
import Project.Gpt2CachedStep.ArtifactCode19
import Project.Gpt2CachedStep.ArtifactCode20
import Project.Gpt2CachedStep.ArtifactCode21
import Project.Gpt2CachedStep.ArtifactCode22
import Project.Gpt2CachedStep.ArtifactCode23
import Project.Gpt2CachedStep.ArtifactCode24
import Project.Gpt2CachedStep.ArtifactCode25
import Project.Gpt2CachedStep.ArtifactCode26
import Project.Gpt2CachedStep.ArtifactCode27
import Project.Gpt2CachedStep.ArtifactCode28
import Project.Gpt2CachedStep.ArtifactCode29
import Project.Gpt2CachedStep.ArtifactCode30
import Project.Gpt2CachedStep.ArtifactCode31
import Project.Gpt2CachedStep.ArtifactCode32
import Project.Gpt2CachedStep.ArtifactCode33
import Project.Gpt2CachedStep.ArtifactCode34
import Project.Gpt2CachedStep.ArtifactCode35
import Project.Gpt2CachedStep.ArtifactCode36
import Project.Gpt2CachedStep.ArtifactCode37
import Project.Gpt2CachedStep.ArtifactCode38
import Project.Gpt2CachedStep.ArtifactCode39
import Project.Gpt2CachedStep.ArtifactCode40
import Project.Gpt2CachedStep.ArtifactCode41
import Project.Gpt2CachedStep.ArtifactCode42

namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail43 :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 19083, limit := 19083 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by rfl

theorem codes_tail42 :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 18730, limit := 19083 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43

theorem codes_tail41 :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 18649, limit := 19083 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42

theorem codes_tail40 :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 18621, limit := 19083 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41

theorem codes_tail39 :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 18254, limit := 19083 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40

theorem codes_tail38 :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 17671, limit := 19083 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39

theorem codes_tail37 :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 16952, limit := 19083 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38

theorem codes_tail36 :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 14604, limit := 19083 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37

theorem codes_tail35 :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 14581, limit := 19083 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36

theorem codes_tail34 :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 14558, limit := 19083 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35

theorem codes_tail33 :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 12388, limit := 19083 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34

theorem codes_tail32 :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 11854, limit := 19083 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33

theorem codes_tail31 :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 11622, limit := 19083 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32

theorem codes_tail30 :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 11065, limit := 19083 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31

theorem codes_tail29 :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 7346, limit := 19083 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30

theorem codes_tail28 :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 7130, limit := 19083 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29

theorem codes_tail27 :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 6748, limit := 19083 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28

theorem codes_tail26 :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 6268, limit := 19083 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27

theorem codes_tail25 :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 5824, limit := 19083 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26

theorem codes_tail24 :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 5648, limit := 19083 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25

theorem codes_tail23 :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 5273, limit := 19083 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24

theorem codes_tail22 :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 5051, limit := 19083 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23

theorem codes_tail21 :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 4096, limit := 19083 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22

theorem codes_tail20 :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 1956, limit := 19083 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21

theorem codes_tail19 :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 1664, limit := 19083 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20

theorem codes_tail18 :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 1433, limit := 19083 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19

theorem codes_tail17 :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 1344, limit := 19083 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18

theorem codes_tail16 :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 1297, limit := 19083 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17

theorem codes_tail15 :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 1262, limit := 19083 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16

theorem codes_tail14 :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 1193, limit := 19083 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15

theorem codes_tail13 :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 1158, limit := 19083 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14

theorem codes_tail12 :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 1087, limit := 19083 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13

theorem codes_tail11 :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 1052, limit := 19083 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12

theorem codes_tail10 :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 981, limit := 19083 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11

theorem codes_tail9 :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 946, limit := 19083 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10

theorem codes_tail8 :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 911, limit := 19083 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9

theorem codes_tail7 :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 876, limit := 19083 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8

theorem codes_tail6 :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 805, limit := 19083 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 770, limit := 19083 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 698, limit := 19083 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 686, limit := 19083 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 615, limit := 19083 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 566, limit := 19083 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 553, limit := 19083 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 552, limit := 19083 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine vector_eq_of_parts (length := 43)
    (itemsStart := { bytes := artifactBytes, pos := 553, limit := 19083 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 549, limit := 19083 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 19083, limit := 19083 }) := by
  refine sized_eq_of_parts (size := 18531)
    (payload := { bytes := artifactBytes, pos := 552, limit := 19083 }) (finish := { bytes := artifactBytes, pos := 19083, limit := 19083 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.Gpt2CachedStep.Artifact
