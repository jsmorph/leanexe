import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_tail1_decoded :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 1426, limit := 1555 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 1, .end), { bytes := artifactBytes, pos := 1555, limit := 1555 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1424, limit := 1555 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1555, limit := 1555 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1419, limit := 4936 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1555, limit := 4936 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1421, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1424, limit := 1555 })
    (bodyFinish := { bytes := artifactBytes, pos := 1555, limit := 1555 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_17_t_tail28_decoded :
    instructionSequenceAt 279 true { bytes := artifactBytes, pos := 1749, limit := 1886 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 1878, limit := 1886 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_17_t_tail0_decoded :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1651, limit := 1886 } =
      .ok ((((((Cache.raw.codes[17]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1878, limit := 1886 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail17_decoded :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1649, limit := 1886 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 17, .end), { bytes := artifactBytes, pos := 1886, limit := 1886 }) := by
  cbv

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1560, limit := 1886 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1886, limit := 1886 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1555, limit := 4936 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 1886, limit := 4936 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1557, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1560, limit := 1886 })
    (bodyFinish := { bytes := artifactBytes, pos := 1886, limit := 1886 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 1890, limit := 1969 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1969, limit := 1969 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 1886, limit := 4936 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 1969, limit := 4936 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 1887, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1890, limit := 1969 })
    (bodyFinish := { bytes := artifactBytes, pos := 1969, limit := 1969 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 1973, limit := 2038 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2038, limit := 2038 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 1969, limit := 4936 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2038, limit := 4936 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 1970, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 1973, limit := 2038 })
    (bodyFinish := { bytes := artifactBytes, pos := 2038, limit := 2038 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded

@[cbv_eval] theorem code20_seq_20_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2042, limit := 2107 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2107, limit := 2107 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2038, limit := 4936 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2107, limit := 4936 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2039, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2042, limit := 2107 })
    (bodyFinish := { bytes := artifactBytes, pos := 2107, limit := 2107 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code20_seq_20_tail0_decoded
  · rfl

#print axioms code20_decoded

@[cbv_eval] theorem code21_seq_21_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2111, limit := 2163 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2163, limit := 2163 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2107, limit := 4936 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2163, limit := 4936 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2108, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2111, limit := 2163 })
    (bodyFinish := { bytes := artifactBytes, pos := 2163, limit := 2163 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code21_seq_21_tail0_decoded
  · rfl

#print axioms code21_decoded

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2167, limit := 2180 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2180, limit := 2180 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2163, limit := 4936 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2180, limit := 4936 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 2164, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2167, limit := 2180 })
    (bodyFinish := { bytes := artifactBytes, pos := 2180, limit := 2180 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2184, limit := 2307 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2307, limit := 2307 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2180, limit := 4936 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2307, limit := 4936 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2181, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 2184, limit := 2307 })
    (bodyFinish := { bytes := artifactBytes, pos := 2307, limit := 2307 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded

end Project.EulerOutwardSpeed.Artifact
