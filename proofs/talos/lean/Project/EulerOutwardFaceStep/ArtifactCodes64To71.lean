import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code64_seq_64_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6932, limit := 6939 } =
      .ok ((((Cache.raw.codes[64]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6939, limit := 6939 }) := by
  cbv

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 6928, limit := 9077 } =
      .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 6939, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6929, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6932, limit := 6939 })
    (bodyFinish := { bytes := artifactBytes, pos := 6939, limit := 6939 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code64_seq_64_tail0_decoded
  · rfl

#print axioms code64_decoded

@[cbv_eval] theorem code65_seq_65_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6943, limit := 6950 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6950, limit := 6950 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 6939, limit := 9077 } =
      .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 6950, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6940, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6943, limit := 6950 })
    (bodyFinish := { bytes := artifactBytes, pos := 6950, limit := 6950 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code65_seq_65_tail0_decoded
  · rfl

#print axioms code65_decoded

@[cbv_eval] theorem code66_seq_66_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6954, limit := 6961 } =
      .ok ((((Cache.raw.codes[66]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6961, limit := 6961 }) := by
  cbv

theorem code66_decoded :
    code { bytes := artifactBytes, pos := 6950, limit := 9077 } =
      .ok (Cache.raw.codes[66]!, { bytes := artifactBytes, pos := 6961, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6951, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6954, limit := 6961 })
    (bodyFinish := { bytes := artifactBytes, pos := 6961, limit := 6961 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code66_seq_66_tail0_decoded
  · rfl

#print axioms code66_decoded

@[cbv_eval] theorem code67_seq_67_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6965, limit := 6972 } =
      .ok ((((Cache.raw.codes[67]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6972, limit := 6972 }) := by
  cbv

theorem code67_decoded :
    code { bytes := artifactBytes, pos := 6961, limit := 9077 } =
      .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 6972, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6962, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6965, limit := 6972 })
    (bodyFinish := { bytes := artifactBytes, pos := 6972, limit := 6972 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code67_seq_67_tail0_decoded
  · rfl

#print axioms code67_decoded

@[cbv_eval] theorem code68_seq_68_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 6976, limit := 7025 } =
      .ok ((((Cache.raw.codes[68]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7025, limit := 7025 }) := by
  cbv

theorem code68_decoded :
    code { bytes := artifactBytes, pos := 6972, limit := 9077 } =
      .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 7025, limit := 9077 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 6973, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6976, limit := 7025 })
    (bodyFinish := { bytes := artifactBytes, pos := 7025, limit := 7025 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code68_seq_68_tail0_decoded
  · rfl

#print axioms code68_decoded

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_93_t_tail19_decoded :
    instructionSequenceAt 688 true { bytes := artifactBytes, pos := 7551, limit := 7902 } =
      .ok ((((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 19, .otherwise), { bytes := artifactBytes, pos := 7678, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_93_t_tail0_decoded :
    instructionSequenceAt 707 true { bytes := artifactBytes, pos := 7513, limit := 7902 } =
      .ok ((((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7678, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_tail94_decoded :
    instructionSequenceAt 708 true { bytes := artifactBytes, pos := 7729, limit := 7902 } =
      .ok ((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 94, .otherwise), { bytes := artifactBytes, pos := 7730, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_tail93_decoded :
    instructionSequenceAt 709 true { bytes := artifactBytes, pos := 7511, limit := 7902 } =
      .ok ((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 93, .otherwise), { bytes := artifactBytes, pos := 7730, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_tail67_decoded :
    instructionSequenceAt 735 true { bytes := artifactBytes, pos := 7384, limit := 7902 } =
      .ok ((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 67, .otherwise), { bytes := artifactBytes, pos := 7730, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_tail3_decoded :
    instructionSequenceAt 799 true { bytes := artifactBytes, pos := 7256, limit := 7902 } =
      .ok ((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 3, .otherwise), { bytes := artifactBytes, pos := 7730, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_31_t_tail0_decoded :
    instructionSequenceAt 802 true { bytes := artifactBytes, pos := 7250, limit := 7902 } =
      .ok ((((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7730, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_tail32_decoded :
    instructionSequenceAt 803 true { bytes := artifactBytes, pos := 7781, limit := 7902 } =
      .ok ((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 7782, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_tail31_decoded :
    instructionSequenceAt 804 true { bytes := artifactBytes, pos := 7248, limit := 7902 } =
      .ok ((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false).drop 31, .otherwise), { bytes := artifactBytes, pos := 7782, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_17_t_tail0_decoded :
    instructionSequenceAt 835 true { bytes := artifactBytes, pos := 7157, limit := 7902 } =
      .ok ((((((((Cache.raw.codes[69]!).body)[16]!).childBody false)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7782, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_tail18_decoded :
    instructionSequenceAt 836 true { bytes := artifactBytes, pos := 7833, limit := 7902 } =
      .ok ((((((Cache.raw.codes[69]!).body)[16]!).childBody false).drop 18, .otherwise), { bytes := artifactBytes, pos := 7834, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_tail17_decoded :
    instructionSequenceAt 837 true { bytes := artifactBytes, pos := 7155, limit := 7902 } =
      .ok ((((((Cache.raw.codes[69]!).body)[16]!).childBody false).drop 17, .otherwise), { bytes := artifactBytes, pos := 7834, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_16_t_tail0_decoded :
    instructionSequenceAt 854 true { bytes := artifactBytes, pos := 7113, limit := 7902 } =
      .ok ((((((Cache.raw.codes[69]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7834, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_tail17_decoded :
    instructionSequenceAt 855 false { bytes := artifactBytes, pos := 7885, limit := 7902 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 17, .end), { bytes := artifactBytes, pos := 7902, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_tail16_decoded :
    instructionSequenceAt 856 false { bytes := artifactBytes, pos := 7111, limit := 7902 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 16, .end), { bytes := artifactBytes, pos := 7902, limit := 7902 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_tail0_decoded :
    instructionSequenceAt 872 false { bytes := artifactBytes, pos := 7030, limit := 7902 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7902, limit := 7902 }) := by
  cbv

theorem code69_decoded :
    code { bytes := artifactBytes, pos := 7025, limit := 9077 } =
      .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 7902, limit := 9077 }) := by
  refine code_eq_of_parts (size := 875)
    (payload := { bytes := artifactBytes, pos := 7027, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 7030, limit := 7902 })
    (bodyFinish := { bytes := artifactBytes, pos := 7902, limit := 7902 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code69_seq_69_tail0_decoded
  · rfl

#print axioms code69_decoded

@[cbv_eval] theorem code70_seq_70_tail107_decoded :
    instructionSequenceAt 234 false { bytes := artifactBytes, pos := 8121, limit := 8248 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 107, .end), { bytes := artifactBytes, pos := 8248, limit := 8248 }) := by
  cbv

@[cbv_eval] theorem code70_seq_70_tail43_decoded :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 7993, limit := 8248 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 43, .end), { bytes := artifactBytes, pos := 8248, limit := 8248 }) := by
  cbv

@[cbv_eval] theorem code70_seq_70_tail0_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 7907, limit := 8248 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8248, limit := 8248 }) := by
  cbv

theorem code70_decoded :
    code { bytes := artifactBytes, pos := 7902, limit := 9077 } =
      .ok (Cache.raw.codes[70]!, { bytes := artifactBytes, pos := 8248, limit := 9077 }) := by
  refine code_eq_of_parts (size := 344)
    (payload := { bytes := artifactBytes, pos := 7904, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 7907, limit := 8248 })
    (bodyFinish := { bytes := artifactBytes, pos := 8248, limit := 8248 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code70_seq_70_tail0_decoded
  · rfl

#print axioms code70_decoded

@[cbv_eval] theorem code71_seq_71_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 8325, limit := 8615 } =
      .ok ((((((((Cache.raw.codes[71]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8453, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 8294, limit := 8615 } =
      .ok ((((((((Cache.raw.codes[71]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8453, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_18_t_tail1_decoded :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 8453, limit := 8615 } =
      .ok ((((((Cache.raw.codes[71]!).body)[18]!).childBody false).drop 1, .end), { bytes := artifactBytes, pos := 8454, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 8292, limit := 8615 } =
      .ok ((((((Cache.raw.codes[71]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8454, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_22_t_tail9_decoded :
    instructionSequenceAt 329 true { bytes := artifactBytes, pos := 8478, limit := 8615 } =
      .ok ((((((Cache.raw.codes[71]!).body)[22]!).childBody false).drop 9, .end), { bytes := artifactBytes, pos := 8605, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 8461, limit := 8615 } =
      .ok ((((((Cache.raw.codes[71]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8605, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail23_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 8605, limit := 8615 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 23, .end), { bytes := artifactBytes, pos := 8615, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 8459, limit := 8615 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 22, .end), { bytes := artifactBytes, pos := 8615, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail19_decoded :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 8454, limit := 8615 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 19, .end), { bytes := artifactBytes, pos := 8615, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 8290, limit := 8615 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 18, .end), { bytes := artifactBytes, pos := 8615, limit := 8615 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 8253, limit := 8615 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8615, limit := 8615 }) := by
  cbv

theorem code71_decoded :
    code { bytes := artifactBytes, pos := 8248, limit := 9077 } =
      .ok (Cache.raw.codes[71]!, { bytes := artifactBytes, pos := 8615, limit := 9077 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 8250, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 8253, limit := 8615 })
    (bodyFinish := { bytes := artifactBytes, pos := 8615, limit := 8615 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code71_seq_71_tail0_decoded
  · rfl

#print axioms code71_decoded


end Project.EulerOutwardFaceStep.Artifact
