import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode0
import Project.Gpt2QuantizedCached.ArtifactCode1
import Project.Gpt2QuantizedCached.ArtifactCode2
import Project.Gpt2QuantizedCached.ArtifactCode3
import Project.Gpt2QuantizedCached.ArtifactCode4
import Project.Gpt2QuantizedCached.ArtifactCode5
import Project.Gpt2QuantizedCached.ArtifactCode6
import Project.Gpt2QuantizedCached.ArtifactCode7
import Project.Gpt2QuantizedCached.ArtifactCode8
import Project.Gpt2QuantizedCached.ArtifactCode9
import Project.Gpt2QuantizedCached.ArtifactCode10
import Project.Gpt2QuantizedCached.ArtifactCode11
import Project.Gpt2QuantizedCached.ArtifactCode12
import Project.Gpt2QuantizedCached.ArtifactCode13
import Project.Gpt2QuantizedCached.ArtifactCode14
import Project.Gpt2QuantizedCached.ArtifactCode15
import Project.Gpt2QuantizedCached.ArtifactCode16
import Project.Gpt2QuantizedCached.ArtifactCode17
import Project.Gpt2QuantizedCached.ArtifactCode18
import Project.Gpt2QuantizedCached.ArtifactCode19
import Project.Gpt2QuantizedCached.ArtifactCode20
import Project.Gpt2QuantizedCached.ArtifactCode21
import Project.Gpt2QuantizedCached.ArtifactCode22
import Project.Gpt2QuantizedCached.ArtifactCode23
import Project.Gpt2QuantizedCached.ArtifactCode24
import Project.Gpt2QuantizedCached.ArtifactCode25
import Project.Gpt2QuantizedCached.ArtifactCode26
import Project.Gpt2QuantizedCached.ArtifactCode27
import Project.Gpt2QuantizedCached.ArtifactCode28
import Project.Gpt2QuantizedCached.ArtifactCode29
import Project.Gpt2QuantizedCached.ArtifactCode30
import Project.Gpt2QuantizedCached.ArtifactCode31
import Project.Gpt2QuantizedCached.ArtifactCode32
import Project.Gpt2QuantizedCached.ArtifactCode33
import Project.Gpt2QuantizedCached.ArtifactCode34
import Project.Gpt2QuantizedCached.ArtifactCode35
import Project.Gpt2QuantizedCached.ArtifactCode36
import Project.Gpt2QuantizedCached.ArtifactCode37
import Project.Gpt2QuantizedCached.ArtifactCode38
import Project.Gpt2QuantizedCached.ArtifactCode39
import Project.Gpt2QuantizedCached.ArtifactCode40
import Project.Gpt2QuantizedCached.ArtifactCode41
import Project.Gpt2QuantizedCached.ArtifactCode42
import Project.Gpt2QuantizedCached.ArtifactCode43
import Project.Gpt2QuantizedCached.ArtifactCode44
import Project.Gpt2QuantizedCached.ArtifactCode45
import Project.Gpt2QuantizedCached.ArtifactCode46
import Project.Gpt2QuantizedCached.ArtifactCode47
import Project.Gpt2QuantizedCached.ArtifactCode48
import Project.Gpt2QuantizedCached.ArtifactCode49
import Project.Gpt2QuantizedCached.ArtifactCode50
import Project.Gpt2QuantizedCached.ArtifactCode51
import Project.Gpt2QuantizedCached.ArtifactCode52
import Project.Gpt2QuantizedCached.ArtifactCode53
import Project.Gpt2QuantizedCached.ArtifactCode54
import Project.Gpt2QuantizedCached.ArtifactCode55
import Project.Gpt2QuantizedCached.ArtifactCode56
import Project.Gpt2QuantizedCached.ArtifactCode57
import Project.Gpt2QuantizedCached.ArtifactCode58
import Project.Gpt2QuantizedCached.ArtifactCode59
import Project.Gpt2QuantizedCached.ArtifactCode60
import Project.Gpt2QuantizedCached.ArtifactCode61
import Project.Gpt2QuantizedCached.ArtifactCode62
import Project.Gpt2QuantizedCached.ArtifactCode63
import Project.Gpt2QuantizedCached.ArtifactCode64
import Project.Gpt2QuantizedCached.ArtifactCode65

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail66 :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 28017, limit := 28017 } =
      .ok (Cache.raw.codes.drop 66, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by rfl

theorem codes_tail65 :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 27664, limit := 28017 } =
      .ok (Cache.raw.codes.drop 65, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code65_decoded codes_tail66

theorem codes_tail64 :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 27583, limit := 28017 } =
      .ok (Cache.raw.codes.drop 64, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code64_decoded codes_tail65

theorem codes_tail63 :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 27555, limit := 28017 } =
      .ok (Cache.raw.codes.drop 63, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code63_decoded codes_tail64

theorem codes_tail62 :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 27188, limit := 28017 } =
      .ok (Cache.raw.codes.drop 62, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code62_decoded codes_tail63

theorem codes_tail61 :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 27134, limit := 28017 } =
      .ok (Cache.raw.codes.drop 61, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code61_decoded codes_tail62

theorem codes_tail60 :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 27117, limit := 28017 } =
      .ok (Cache.raw.codes.drop 60, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code60_decoded codes_tail61

theorem codes_tail59 :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 25750, limit := 28017 } =
      .ok (Cache.raw.codes.drop 59, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code59_decoded codes_tail60

theorem codes_tail58 :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 23674, limit := 28017 } =
      .ok (Cache.raw.codes.drop 58, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code58_decoded codes_tail59

theorem codes_tail57 :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 23651, limit := 28017 } =
      .ok (Cache.raw.codes.drop 57, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code57_decoded codes_tail58

theorem codes_tail56 :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 23628, limit := 28017 } =
      .ok (Cache.raw.codes.drop 56, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code56_decoded codes_tail57

theorem codes_tail55 :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 23617, limit := 28017 } =
      .ok (Cache.raw.codes.drop 55, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code55_decoded codes_tail56

theorem codes_tail54 :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 20697, limit := 28017 } =
      .ok (Cache.raw.codes.drop 54, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code54_decoded codes_tail55

theorem codes_tail53 :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 20163, limit := 28017 } =
      .ok (Cache.raw.codes.drop 53, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code53_decoded codes_tail54

theorem codes_tail52 :
    Internal.vectorLoop code 14 { bytes := artifactBytes, pos := 19931, limit := 28017 } =
      .ok (Cache.raw.codes.drop 52, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code52_decoded codes_tail53

theorem codes_tail51 :
    Internal.vectorLoop code 15 { bytes := artifactBytes, pos := 19374, limit := 28017 } =
      .ok (Cache.raw.codes.drop 51, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code51_decoded codes_tail52

theorem codes_tail50 :
    Internal.vectorLoop code 16 { bytes := artifactBytes, pos := 15663, limit := 28017 } =
      .ok (Cache.raw.codes.drop 50, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code50_decoded codes_tail51

theorem codes_tail49 :
    Internal.vectorLoop code 17 { bytes := artifactBytes, pos := 15455, limit := 28017 } =
      .ok (Cache.raw.codes.drop 49, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code49_decoded codes_tail50

theorem codes_tail48 :
    Internal.vectorLoop code 18 { bytes := artifactBytes, pos := 15089, limit := 28017 } =
      .ok (Cache.raw.codes.drop 48, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code48_decoded codes_tail49

theorem codes_tail47 :
    Internal.vectorLoop code 19 { bytes := artifactBytes, pos := 14609, limit := 28017 } =
      .ok (Cache.raw.codes.drop 47, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code47_decoded codes_tail48

theorem codes_tail46 :
    Internal.vectorLoop code 20 { bytes := artifactBytes, pos := 14173, limit := 28017 } =
      .ok (Cache.raw.codes.drop 46, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code46_decoded codes_tail47

theorem codes_tail45 :
    Internal.vectorLoop code 21 { bytes := artifactBytes, pos := 13997, limit := 28017 } =
      .ok (Cache.raw.codes.drop 45, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code45_decoded codes_tail46

theorem codes_tail44 :
    Internal.vectorLoop code 22 { bytes := artifactBytes, pos := 13630, limit := 28017 } =
      .ok (Cache.raw.codes.drop 44, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code44_decoded codes_tail45

theorem codes_tail43 :
    Internal.vectorLoop code 23 { bytes := artifactBytes, pos := 13408, limit := 28017 } =
      .ok (Cache.raw.codes.drop 43, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code43_decoded codes_tail44

theorem codes_tail42 :
    Internal.vectorLoop code 24 { bytes := artifactBytes, pos := 11167, limit := 28017 } =
      .ok (Cache.raw.codes.drop 42, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code42_decoded codes_tail43

theorem codes_tail41 :
    Internal.vectorLoop code 25 { bytes := artifactBytes, pos := 11144, limit := 28017 } =
      .ok (Cache.raw.codes.drop 41, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code41_decoded codes_tail42

theorem codes_tail40 :
    Internal.vectorLoop code 26 { bytes := artifactBytes, pos := 11107, limit := 28017 } =
      .ok (Cache.raw.codes.drop 40, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code40_decoded codes_tail41

theorem codes_tail39 :
    Internal.vectorLoop code 27 { bytes := artifactBytes, pos := 11084, limit := 28017 } =
      .ok (Cache.raw.codes.drop 39, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code39_decoded codes_tail40

theorem codes_tail38 :
    Internal.vectorLoop code 28 { bytes := artifactBytes, pos := 10827, limit := 28017 } =
      .ok (Cache.raw.codes.drop 38, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code38_decoded codes_tail39

theorem codes_tail37 :
    Internal.vectorLoop code 29 { bytes := artifactBytes, pos := 9671, limit := 28017 } =
      .ok (Cache.raw.codes.drop 37, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code37_decoded codes_tail38

theorem codes_tail36 :
    Internal.vectorLoop code 30 { bytes := artifactBytes, pos := 9568, limit := 28017 } =
      .ok (Cache.raw.codes.drop 36, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code36_decoded codes_tail37

theorem codes_tail35 :
    Internal.vectorLoop code 31 { bytes := artifactBytes, pos := 9227, limit := 28017 } =
      .ok (Cache.raw.codes.drop 35, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code35_decoded codes_tail36

theorem codes_tail34 :
    Internal.vectorLoop code 32 { bytes := artifactBytes, pos := 7095, limit := 28017 } =
      .ok (Cache.raw.codes.drop 34, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code34_decoded codes_tail35

theorem codes_tail33 :
    Internal.vectorLoop code 33 { bytes := artifactBytes, pos := 6811, limit := 28017 } =
      .ok (Cache.raw.codes.drop 33, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code33_decoded codes_tail34

theorem codes_tail32 :
    Internal.vectorLoop code 34 { bytes := artifactBytes, pos := 6588, limit := 28017 } =
      .ok (Cache.raw.codes.drop 32, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code32_decoded codes_tail33

theorem codes_tail31 :
    Internal.vectorLoop code 35 { bytes := artifactBytes, pos := 6499, limit := 28017 } =
      .ok (Cache.raw.codes.drop 31, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code31_decoded codes_tail32

theorem codes_tail30 :
    Internal.vectorLoop code 36 { bytes := artifactBytes, pos := 5618, limit := 28017 } =
      .ok (Cache.raw.codes.drop 30, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code30_decoded codes_tail31

theorem codes_tail29 :
    Internal.vectorLoop code 37 { bytes := artifactBytes, pos := 5571, limit := 28017 } =
      .ok (Cache.raw.codes.drop 29, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code29_decoded codes_tail30

theorem codes_tail28 :
    Internal.vectorLoop code 38 { bytes := artifactBytes, pos := 4592, limit := 28017 } =
      .ok (Cache.raw.codes.drop 28, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code28_decoded codes_tail29

theorem codes_tail27 :
    Internal.vectorLoop code 39 { bytes := artifactBytes, pos := 3566, limit := 28017 } =
      .ok (Cache.raw.codes.drop 27, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code27_decoded codes_tail28

theorem codes_tail26 :
    Internal.vectorLoop code 40 { bytes := artifactBytes, pos := 3318, limit := 28017 } =
      .ok (Cache.raw.codes.drop 26, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code26_decoded codes_tail27

theorem codes_tail25 :
    Internal.vectorLoop code 41 { bytes := artifactBytes, pos := 3278, limit := 28017 } =
      .ok (Cache.raw.codes.drop 25, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code25_decoded codes_tail26

theorem codes_tail24 :
    Internal.vectorLoop code 42 { bytes := artifactBytes, pos := 3015, limit := 28017 } =
      .ok (Cache.raw.codes.drop 24, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code24_decoded codes_tail25

theorem codes_tail23 :
    Internal.vectorLoop code 43 { bytes := artifactBytes, pos := 2808, limit := 28017 } =
      .ok (Cache.raw.codes.drop 23, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code23_decoded codes_tail24

theorem codes_tail22 :
    Internal.vectorLoop code 44 { bytes := artifactBytes, pos := 2230, limit := 28017 } =
      .ok (Cache.raw.codes.drop 22, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code22_decoded codes_tail23

theorem codes_tail21 :
    Internal.vectorLoop code 45 { bytes := artifactBytes, pos := 2160, limit := 28017 } =
      .ok (Cache.raw.codes.drop 21, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code21_decoded codes_tail22

theorem codes_tail20 :
    Internal.vectorLoop code 46 { bytes := artifactBytes, pos := 2091, limit := 28017 } =
      .ok (Cache.raw.codes.drop 20, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code20_decoded codes_tail21

theorem codes_tail19 :
    Internal.vectorLoop code 47 { bytes := artifactBytes, pos := 2021, limit := 28017 } =
      .ok (Cache.raw.codes.drop 19, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code19_decoded codes_tail20

theorem codes_tail18 :
    Internal.vectorLoop code 48 { bytes := artifactBytes, pos := 1951, limit := 28017 } =
      .ok (Cache.raw.codes.drop 18, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code18_decoded codes_tail19

theorem codes_tail17 :
    Internal.vectorLoop code 49 { bytes := artifactBytes, pos := 1880, limit := 28017 } =
      .ok (Cache.raw.codes.drop 17, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code17_decoded codes_tail18

theorem codes_tail16 :
    Internal.vectorLoop code 50 { bytes := artifactBytes, pos := 1810, limit := 28017 } =
      .ok (Cache.raw.codes.drop 16, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code16_decoded codes_tail17

theorem codes_tail15 :
    Internal.vectorLoop code 51 { bytes := artifactBytes, pos := 1740, limit := 28017 } =
      .ok (Cache.raw.codes.drop 15, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code15_decoded codes_tail16

theorem codes_tail14 :
    Internal.vectorLoop code 52 { bytes := artifactBytes, pos := 1669, limit := 28017 } =
      .ok (Cache.raw.codes.drop 14, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code14_decoded codes_tail15

theorem codes_tail13 :
    Internal.vectorLoop code 53 { bytes := artifactBytes, pos := 1599, limit := 28017 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code13_decoded codes_tail14

theorem codes_tail12 :
    Internal.vectorLoop code 54 { bytes := artifactBytes, pos := 1529, limit := 28017 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13

theorem codes_tail11 :
    Internal.vectorLoop code 55 { bytes := artifactBytes, pos := 1459, limit := 28017 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12

theorem codes_tail10 :
    Internal.vectorLoop code 56 { bytes := artifactBytes, pos := 1389, limit := 28017 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11

theorem codes_tail9 :
    Internal.vectorLoop code 57 { bytes := artifactBytes, pos := 1318, limit := 28017 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10

theorem codes_tail8 :
    Internal.vectorLoop code 58 { bytes := artifactBytes, pos := 1248, limit := 28017 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9

theorem codes_tail7 :
    Internal.vectorLoop code 59 { bytes := artifactBytes, pos := 1178, limit := 28017 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8

theorem codes_tail6 :
    Internal.vectorLoop code 60 { bytes := artifactBytes, pos := 1107, limit := 28017 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 61 { bytes := artifactBytes, pos := 1060, limit := 28017 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 62 { bytes := artifactBytes, pos := 954, limit := 28017 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 63 { bytes := artifactBytes, pos := 883, limit := 28017 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 64 { bytes := artifactBytes, pos := 811, limit := 28017 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 65 { bytes := artifactBytes, pos := 796, limit := 28017 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 66 { bytes := artifactBytes, pos := 785, limit := 28017 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 784, limit := 28017 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  refine vector_eq_of_parts (length := 66)
    (itemsStart := { bytes := artifactBytes, pos := 785, limit := 28017 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 781, limit := 28017 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 28017, limit := 28017 }) := by
  refine sized_eq_of_parts (size := 27233)
    (payload := { bytes := artifactBytes, pos := 784, limit := 28017 }) (finish := { bytes := artifactBytes, pos := 28017, limit := 28017 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.Gpt2QuantizedCached.Artifact
