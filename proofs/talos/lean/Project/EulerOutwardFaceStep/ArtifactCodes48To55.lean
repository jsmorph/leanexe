import Project.EulerOutwardFaceStep.ArtifactByteLookup
import Project.EulerOutwardFaceStep.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFaceStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code48_seq_48_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5812, limit := 5819 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5819, limit := 5819 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 5808, limit := 9077 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 5819, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5809, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5812, limit := 5819 })
    (bodyFinish := { bytes := artifactBytes, pos := 5819, limit := 5819 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_seq_48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_seq_49_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5823, limit := 5830 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5830, limit := 5830 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 5819, limit := 9077 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 5830, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5820, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5823, limit := 5830 })
    (bodyFinish := { bytes := artifactBytes, pos := 5830, limit := 5830 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_seq_49_tail0_decoded
  · rfl

#print axioms code49_decoded

@[cbv_eval] theorem code50_seq_50_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5834, limit := 5841 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5841, limit := 5841 }) := by
  cbv

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 5830, limit := 9077 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 5841, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5831, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5834, limit := 5841 })
    (bodyFinish := { bytes := artifactBytes, pos := 5841, limit := 5841 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code50_seq_50_tail0_decoded
  · rfl

#print axioms code50_decoded

@[cbv_eval] theorem code51_seq_51_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5845, limit := 5852 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5852, limit := 5852 }) := by
  cbv

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 5841, limit := 9077 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 5852, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5842, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5845, limit := 5852 })
    (bodyFinish := { bytes := artifactBytes, pos := 5852, limit := 5852 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code51_seq_51_tail0_decoded
  · rfl

#print axioms code51_decoded

@[cbv_eval] theorem code52_seq_52_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5856, limit := 5863 } =
      .ok ((((Cache.raw.codes[52]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5863, limit := 5863 }) := by
  cbv

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 5852, limit := 9077 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 5863, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5853, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5856, limit := 5863 })
    (bodyFinish := { bytes := artifactBytes, pos := 5863, limit := 5863 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code52_seq_52_tail0_decoded
  · rfl

#print axioms code52_decoded

@[cbv_eval] theorem code53_seq_53_tail0_decoded :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 5867, limit := 5904 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5904, limit := 5904 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 5863, limit := 9077 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 5904, limit := 9077 }) := by
  refine code_eq_of_parts (size := 40)
    (payload := { bytes := artifactBytes, pos := 5864, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5867, limit := 5904 })
    (bodyFinish := { bytes := artifactBytes, pos := 5904, limit := 5904 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code53_seq_53_tail0_decoded
  · rfl

#print axioms code53_decoded

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail102_decoded :
    instructionSequenceAt 459 true { bytes := artifactBytes, pos := 6355, limit := 6560 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 102, .otherwise), { bytes := artifactBytes, pos := 6468, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail61_decoded :
    instructionSequenceAt 500 true { bytes := artifactBytes, pos := 6228, limit := 6560 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 61, .otherwise), { bytes := artifactBytes, pos := 6468, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_43_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 6101, limit := 6560 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[43]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6468, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail44_decoded :
    instructionSequenceAt 562 true { bytes := artifactBytes, pos := 6507, limit := 6560 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 44, .otherwise), { bytes := artifactBytes, pos := 6508, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail43_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 6099, limit := 6560 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 6508, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_43_t_tail0_decoded :
    instructionSequenceAt 606 true { bytes := artifactBytes, pos := 6005, limit := 6560 } =
      .ok ((((((Cache.raw.codes[54]!).body)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 6508, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail44_decoded :
    instructionSequenceAt 607 false { bytes := artifactBytes, pos := 6547, limit := 6560 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 44, .end), { bytes := artifactBytes, pos := 6560, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail43_decoded :
    instructionSequenceAt 608 false { bytes := artifactBytes, pos := 6003, limit := 6560 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 43, .end), { bytes := artifactBytes, pos := 6560, limit := 6560 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail0_decoded :
    instructionSequenceAt 651 false { bytes := artifactBytes, pos := 5909, limit := 6560 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6560, limit := 6560 }) := by
  cbv

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 5904, limit := 9077 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 6560, limit := 9077 }) := by
  refine code_eq_of_parts (size := 654)
    (payload := { bytes := artifactBytes, pos := 5906, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 5909, limit := 6560 })
    (bodyFinish := { bytes := artifactBytes, pos := 6560, limit := 6560 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code54_seq_54_tail0_decoded
  · rfl

#print axioms code54_decoded

@[cbv_eval] theorem code55_seq_55_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6564, limit := 6571 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6571, limit := 6571 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 6560, limit := 9077 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 6571, limit := 9077 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6561, limit := 9077 })
    (bodyStart := { bytes := artifactBytes, pos := 6564, limit := 6571 })
    (bodyFinish := { bytes := artifactBytes, pos := 6571, limit := 6571 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code55_seq_55_tail0_decoded
  · rfl

#print axioms code55_decoded


end Project.EulerOutwardFaceStep.Artifact
