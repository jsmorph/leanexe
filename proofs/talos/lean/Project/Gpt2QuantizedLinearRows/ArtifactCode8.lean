import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail136 :
    instructionSequenceAt 1329 true { bytes := artifactBytes, pos := 3306, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 136, .otherwise), { bytes := artifactBytes, pos := 3435, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail99 :
    instructionSequenceAt 1366 true { bytes := artifactBytes, pos := 3177, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 99, .otherwise), { bytes := artifactBytes, pos := 3435, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail49 :
    instructionSequenceAt 1416 true { bytes := artifactBytes, pos := 3048, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 3435, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail5 :
    instructionSequenceAt 1460 true { bytes := artifactBytes, pos := 2920, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 5, .otherwise), { bytes := artifactBytes, pos := 3435, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_t_tail0 :
    instructionSequenceAt 1465 true { bytes := artifactBytes, pos := 2910, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3435, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail98 :
    instructionSequenceAt 1367 false { bytes := artifactBytes, pos := 3700, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 98, .end), { bytes := artifactBytes, pos := 3828, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail48 :
    instructionSequenceAt 1417 false { bytes := artifactBytes, pos := 3571, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 48, .end), { bytes := artifactBytes, pos := 3828, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail4 :
    instructionSequenceAt 1461 false { bytes := artifactBytes, pos := 3443, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 4, .end), { bytes := artifactBytes, pos := 3828, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_19_e_tail0 :
    instructionSequenceAt 1465 false { bytes := artifactBytes, pos := 3435, limit := 3928 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 3828, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_0_t_tail18 :
    instructionSequenceAt 1481 false { bytes := artifactBytes, pos := 2573, limit := 3928 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[70]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2701, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_0_t_tail0 :
    instructionSequenceAt 1499 false { bytes := artifactBytes, pos := 2542, limit := 3928 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[70]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2701, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_tail19 :
    instructionSequenceAt 1467 false { bytes := artifactBytes, pos := 2908, limit := 3928 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 3842, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_0_t_tail0 :
    instructionSequenceAt 1486 false { bytes := artifactBytes, pos := 2872, limit := 3928 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[83]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3842, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_70_t_tail0 :
    instructionSequenceAt 1501 false { bytes := artifactBytes, pos := 2540, limit := 3928 } =
      .ok ((((((Cache.raw.codes[8]!).body)[70]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2702, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_74_t_tail8 :
    instructionSequenceAt 1489 true { bytes := artifactBytes, pos := 2722, limit := 3928 } =
      .ok ((((((Cache.raw.codes[8]!).body)[74]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2853, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_74_t_tail0 :
    instructionSequenceAt 1497 true { bytes := artifactBytes, pos := 2709, limit := 3928 } =
      .ok ((((((Cache.raw.codes[8]!).body)[74]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2853, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_83_t_tail0 :
    instructionSequenceAt 1488 false { bytes := artifactBytes, pos := 2870, limit := 3928 } =
      .ok ((((((Cache.raw.codes[8]!).body)[83]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3843, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail83 :
    instructionSequenceAt 1490 false { bytes := artifactBytes, pos := 2868, limit := 3928 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 83, .end), { bytes := artifactBytes, pos := 3928, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail74 :
    instructionSequenceAt 1499 false { bytes := artifactBytes, pos := 2707, limit := 3928 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 74, .end), { bytes := artifactBytes, pos := 3928, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail70 :
    instructionSequenceAt 1503 false { bytes := artifactBytes, pos := 2538, limit := 3928 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 70, .end), { bytes := artifactBytes, pos := 3928, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail27 :
    instructionSequenceAt 1546 false { bytes := artifactBytes, pos := 2409, limit := 3928 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 27, .end), { bytes := artifactBytes, pos := 3928, limit := 3928 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 1573 false { bytes := artifactBytes, pos := 2355, limit := 3928 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3928, limit := 3928 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 2350, limit := 4757 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 3928, limit := 4757 }) := by
  refine code_eq_of_parts (size := 1576)
    (payload := { bytes := artifactBytes, pos := 2352, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 2355, limit := 3928 })
    (bodyFinish := { bytes := artifactBytes, pos := 3928, limit := 3928 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
