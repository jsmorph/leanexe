import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code16_seq_16_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 1805, limit := 2095 } =
      .ok ((((((((Cache.raw.codes[16]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1933, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 1774, limit := 2095 } =
      .ok ((((((((Cache.raw.codes[16]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1933, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_18_t_tail1_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 1933, limit := 2095 } =
      .ok ((((((Cache.raw.codes[16]!).body)[18]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 1934, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 1772, limit := 2095 } =
      .ok ((((((Cache.raw.codes[16]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1934, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_22_t_tail9_decoded :
    instructionSequenceAt 329 true { bytes := artifactBytes, pos := 1958, limit := 2095 } =
      .ok ((((((Cache.raw.codes[16]!).body)[22]!).childBody false).drop 9, .end), { bytes := artifactBytes, pos := 2085, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 1941, limit := 2095 } =
      .ok ((((((Cache.raw.codes[16]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2085, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail23_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 2085, limit := 2095 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 23, .end), { bytes := artifactBytes, pos := 2095, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 1939, limit := 2095 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 22, .end), { bytes := artifactBytes, pos := 2095, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail19_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 1934, limit := 2095 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 19, .end), { bytes := artifactBytes, pos := 2095, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 1770, limit := 2095 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 18, .end), { bytes := artifactBytes, pos := 2095, limit := 2095 }) := by
  cbv

@[cbv_eval] theorem code16_seq_16_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 1733, limit := 2095 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2095, limit := 2095 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1728, limit := 2557 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 2095, limit := 2557 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 1730, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 1733, limit := 2095 })
    (bodyFinish := { bytes := artifactBytes, pos := 2095, limit := 2095 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code16_seq_16_tail0_decoded
  · rfl

#print axioms code16_decoded

@[cbv_eval] theorem code17_seq_17_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 2097, limit := 2123 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2123, limit := 2123 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 2095, limit := 2557 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2123, limit := 2557 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 2096, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 2097, limit := 2123 })
    (bodyFinish := { bytes := artifactBytes, pos := 2123, limit := 2123 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code17_seq_17_tail0_decoded
  · rfl

#print axioms code17_decoded

@[cbv_eval] theorem code18_seq_18_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 2127, limit := 2204 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2204, limit := 2204 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2123, limit := 2557 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2204, limit := 2557 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 2124, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 2127, limit := 2204 })
    (bodyFinish := { bytes := artifactBytes, pos := 2204, limit := 2204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code18_seq_18_tail0_decoded
  · rfl

#print axioms code18_decoded

@[cbv_eval] theorem code19_seq_19_tail44_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 2523, limit := 2557 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 44, .end), { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  cbv

@[cbv_eval] theorem code19_seq_19_tail42_decoded :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 2396, limit := 2557 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 42, .end), { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  cbv

@[cbv_eval] theorem code19_seq_19_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 2268, limit := 2557 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 25, .end), { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  cbv

@[cbv_eval] theorem code19_seq_19_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 2209, limit := 2557 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2204, limit := 2557 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2557, limit := 2557 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 2206, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 2209, limit := 2557 })
    (bodyFinish := { bytes := artifactBytes, pos := 2557, limit := 2557 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code19_seq_19_tail0_decoded
  · rfl

#print axioms code19_decoded


end Project.EulerOutwardCfl.Artifact
