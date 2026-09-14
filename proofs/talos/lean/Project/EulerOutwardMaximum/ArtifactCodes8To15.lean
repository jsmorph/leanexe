import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code8_seq_8_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 934, limit := 972 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 972, limit := 972 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 930, limit := 5260 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 972, limit := 5260 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 931, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 934, limit := 972 })
    (bodyFinish := { bytes := artifactBytes, pos := 972, limit := 972 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code8_seq_8_tail0_decoded
  · rfl

#print axioms code8_decoded

@[cbv_eval] theorem code9_seq_9_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 976, limit := 995 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 995, limit := 995 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 972, limit := 5260 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 995, limit := 5260 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 973, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 976, limit := 995 })
    (bodyFinish := { bytes := artifactBytes, pos := 995, limit := 995 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code9_seq_9_tail0_decoded
  · rfl

#print axioms code9_decoded

@[cbv_eval] theorem code10_seq_10_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 999, limit := 1032 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1032, limit := 1032 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 995, limit := 5260 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1032, limit := 5260 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 996, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 999, limit := 1032 })
    (bodyFinish := { bytes := artifactBytes, pos := 1032, limit := 1032 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code10_seq_10_tail0_decoded
  · rfl

#print axioms code10_decoded

@[cbv_eval] theorem code11_seq_11_tail0_decoded :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1036, limit := 1054 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1054, limit := 1054 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1032, limit := 5260 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1054, limit := 5260 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1033, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1036, limit := 1054 })
    (bodyFinish := { bytes := artifactBytes, pos := 1054, limit := 1054 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code11_seq_11_tail0_decoded
  · rfl

#print axioms code11_decoded

@[cbv_eval] theorem code12_seq_12_tail0_decoded :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1058, limit := 1100 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1100, limit := 1100 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1054, limit := 5260 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1100, limit := 5260 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1055, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1058, limit := 1100 })
    (bodyFinish := { bytes := artifactBytes, pos := 1100, limit := 1100 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code12_seq_12_tail0_decoded
  · rfl

#print axioms code12_decoded

@[cbv_eval] theorem code13_seq_13_tail0_decoded :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1104, limit := 1199 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1199, limit := 1199 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1100, limit := 5260 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1199, limit := 5260 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1101, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1104, limit := 1199 })
    (bodyFinish := { bytes := artifactBytes, pos := 1199, limit := 1199 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code13_seq_13_tail0_decoded
  · rfl

#print axioms code13_decoded

@[cbv_eval] theorem code14_seq_14_tail0_decoded :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1203, limit := 1281 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1281, limit := 1281 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1199, limit := 5260 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1281, limit := 5260 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1200, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1203, limit := 1281 })
    (bodyFinish := { bytes := artifactBytes, pos := 1281, limit := 1281 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code14_seq_14_tail0_decoded
  · rfl

#print axioms code14_decoded

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 28 false { bytes := artifactBytes, pos := 1285, limit := 1313 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1313, limit := 1313 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 1281, limit := 5260 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 1313, limit := 5260 }) := by
  refine code_eq_of_parts (size := 31)
    (payload := { bytes := artifactBytes, pos := 1282, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 1285, limit := 1313 })
    (bodyFinish := { bytes := artifactBytes, pos := 1313, limit := 1313 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded


end Project.EulerOutwardMaximum.Artifact
