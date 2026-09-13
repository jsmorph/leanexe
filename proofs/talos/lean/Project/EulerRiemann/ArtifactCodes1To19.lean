import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Evaluate

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code1_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 1317, limit := 1342 } =
      .ok (((Cache.raw.codes[1]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1342, limit := 1342 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 1313, limit := 21767 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 1342, limit := 21767 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 1314, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1317, limit := 1342 })
    (bodyFinish := { bytes := artifactBytes, pos := 1342, limit := 1342 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 1346, limit := 1384 } =
      .ok (((Cache.raw.codes[2]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1384, limit := 1384 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 1342, limit := 21767 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 1384, limit := 21767 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 1343, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1346, limit := 1384 })
    (bodyFinish := { bytes := artifactBytes, pos := 1384, limit := 1384 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 1388, limit := 1407 } =
      .ok (((Cache.raw.codes[3]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1407, limit := 1407 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 1384, limit := 21767 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 1407, limit := 21767 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 1385, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1388, limit := 1407 })
    (bodyFinish := { bytes := artifactBytes, pos := 1407, limit := 1407 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1411, limit := 1444 } =
      .ok (((Cache.raw.codes[4]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1444, limit := 1444 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 1407, limit := 21767 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 1444, limit := 21767 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 1408, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1411, limit := 1444 })
    (bodyFinish := { bytes := artifactBytes, pos := 1444, limit := 1444 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_tail0_decoded :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 1448, limit := 1572 } =
      .ok (((Cache.raw.codes[5]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1572, limit := 1572 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 1444, limit := 21767 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 1572, limit := 21767 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 1445, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1448, limit := 1572 })
    (bodyFinish := { bytes := artifactBytes, pos := 1572, limit := 1572 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 1576, limit := 1614 } =
      .ok (((Cache.raw.codes[6]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1614, limit := 1614 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 1572, limit := 21767 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 1614, limit := 21767 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 1573, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1576, limit := 1614 })
    (bodyFinish := { bytes := artifactBytes, pos := 1614, limit := 1614 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 1618, limit := 1637 } =
      .ok (((Cache.raw.codes[7]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1637, limit := 1637 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 1614, limit := 21767 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 1637, limit := 21767 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 1615, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1618, limit := 1637 })
    (bodyFinish := { bytes := artifactBytes, pos := 1637, limit := 1637 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_tail0_decoded
  · rfl

#print axioms code7_decoded

@[cbv_eval] theorem code8_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1641, limit := 1674 } =
      .ok (((Cache.raw.codes[8]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1674, limit := 1674 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 1637, limit := 21767 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1674, limit := 21767 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 1638, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1641, limit := 1674 })
    (bodyFinish := { bytes := artifactBytes, pos := 1674, limit := 1674 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1678, limit := 1696 } =
      .ok (((Cache.raw.codes[9]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1696, limit := 1696 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1674, limit := 21767 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1696, limit := 21767 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1675, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1678, limit := 1696 })
    (bodyFinish := { bytes := artifactBytes, pos := 1696, limit := 1696 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1700, limit := 1742 } =
      .ok (((Cache.raw.codes[10]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1742, limit := 1742 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1696, limit := 21767 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1742, limit := 21767 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1697, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1700, limit := 1742 })
    (bodyFinish := { bytes := artifactBytes, pos := 1742, limit := 1742 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1746, limit := 1841 } =
      .ok (((Cache.raw.codes[11]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1841, limit := 1841 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1742, limit := 21767 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1841, limit := 21767 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1743, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1746, limit := 1841 })
    (bodyFinish := { bytes := artifactBytes, pos := 1841, limit := 1841 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1845, limit := 1923 } =
      .ok (((Cache.raw.codes[12]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1923, limit := 1923 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1841, limit := 21767 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1923, limit := 21767 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1842, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1845, limit := 1923 })
    (bodyFinish := { bytes := artifactBytes, pos := 1923, limit := 1923 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1927, limit := 1955 } =
      .ok (((Cache.raw.codes[13]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 1955, limit := 1955 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1923, limit := 21767 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1955, limit := 21767 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1924, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1927, limit := 1955 })
    (bodyFinish := { bytes := artifactBytes, pos := 1955, limit := 1955 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_tail0_decoded :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1959, limit := 2014 } =
      .ok (((Cache.raw.codes[14]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2014, limit := 2014 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1955, limit := 21767 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 2014, limit := 21767 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1956, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 1959, limit := 2014 })
    (bodyFinish := { bytes := artifactBytes, pos := 2014, limit := 2014 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_tail0_decoded :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 2018, limit := 2089 } =
      .ok (((Cache.raw.codes[15]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2089, limit := 2089 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 2014, limit := 21767 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 2089, limit := 21767 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 2015, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2018, limit := 2089 })
    (bodyFinish := { bytes := artifactBytes, pos := 2089, limit := 2089 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_tail0_decoded
  · rfl

#print axioms code15_decoded

@[cbv_eval] theorem code16_tail0_decoded :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 2093, limit := 2205 } =
      .ok (((Cache.raw.codes[16]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2205, limit := 2205 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 2089, limit := 21767 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 2205, limit := 21767 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 2090, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2093, limit := 2205 })
    (bodyFinish := { bytes := artifactBytes, pos := 2205, limit := 2205 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_tail0_decoded :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 2209, limit := 2273 } =
      .ok (((Cache.raw.codes[17]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2273, limit := 2273 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 2205, limit := 21767 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2273, limit := 21767 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 2206, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2209, limit := 2273 })
    (bodyFinish := { bytes := artifactBytes, pos := 2273, limit := 2273 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 2278, limit := 2409 } =
      .ok (((Cache.raw.codes[18]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2409, limit := 2409 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2273, limit := 21767 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2409, limit := 21767 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 2275, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2278, limit := 2409 })
    (bodyFinish := { bytes := artifactBytes, pos := 2409, limit := 2409 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_tail10_decoded :
    instructionSequenceAt 316 false { bytes := artifactBytes, pos := 2480, limit := 2740 } =
      .ok (((Cache.raw.codes[19]!).body.drop 10, .end),
        { bytes := artifactBytes, pos := 2740, limit := 2740 }) := by
  cbv

@[cbv_eval] theorem code19_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 2414, limit := 2740 } =
      .ok (((Cache.raw.codes[19]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 2740, limit := 2740 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2409, limit := 21767 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2740, limit := 21767 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 2411, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2414, limit := 2740 })
    (bodyFinish := { bytes := artifactBytes, pos := 2740, limit := 2740 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_tail0_decoded
  · rfl

#print axioms code19_decoded

end Project.EulerRiemann.Artifact
