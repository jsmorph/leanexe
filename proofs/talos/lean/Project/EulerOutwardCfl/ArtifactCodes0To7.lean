import Project.EulerOutwardCfl.ArtifactByteLookup
import Project.EulerOutwardCfl.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardCfl.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code0_seq_0_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 323, limit := 342 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 342, limit := 342 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 319, limit := 2557 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 342, limit := 2557 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 320, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 323, limit := 342 })
    (bodyFinish := { bytes := artifactBytes, pos := 342, limit := 342 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code0_seq_0_tail0_decoded
  · rfl

#print axioms code0_decoded

@[cbv_eval] theorem code1_seq_1_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 346, limit := 379 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 379, limit := 379 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 342, limit := 2557 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 379, limit := 2557 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 343, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 346, limit := 379 })
    (bodyFinish := { bytes := artifactBytes, pos := 379, limit := 379 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code1_seq_1_tail0_decoded
  · rfl

#print axioms code1_decoded

@[cbv_eval] theorem code2_seq_2_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 383, limit := 448 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 448, limit := 448 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 379, limit := 2557 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 448, limit := 2557 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 380, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 383, limit := 448 })
    (bodyFinish := { bytes := artifactBytes, pos := 448, limit := 448 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code2_seq_2_tail0_decoded
  · rfl

#print axioms code2_decoded

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 452, limit := 517 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 517, limit := 517 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 448, limit := 2557 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 517, limit := 2557 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 449, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 452, limit := 517 })
    (bodyFinish := { bytes := artifactBytes, pos := 517, limit := 517 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 521, limit := 573 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 573, limit := 573 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 517, limit := 2557 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 573, limit := 2557 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 518, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 521, limit := 573 })
    (bodyFinish := { bytes := artifactBytes, pos := 573, limit := 573 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 577, limit := 590 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 590, limit := 590 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 573, limit := 2557 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 590, limit := 2557 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 574, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 577, limit := 590 })
    (bodyFinish := { bytes := artifactBytes, pos := 590, limit := 590 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 594, limit := 717 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 717, limit := 717 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 590, limit := 2557 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 717, limit := 2557 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 591, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 594, limit := 717 })
    (bodyFinish := { bytes := artifactBytes, pos := 717, limit := 717 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 722, limit := 847 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 847, limit := 847 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 717, limit := 2557 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 847, limit := 2557 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 719, limit := 2557 })
    (bodyStart := { bytes := artifactBytes, pos := 722, limit := 847 })
    (bodyFinish := { bytes := artifactBytes, pos := 847, limit := 847 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded


end Project.EulerOutwardCfl.Artifact
