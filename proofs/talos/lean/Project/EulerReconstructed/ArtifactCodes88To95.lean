import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code88_seq_88_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13090, limit := 13097 } =
      .ok ((((Cache.raw.codes[88]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13097, limit := 13097 }) := by
  cbv

theorem code88_decoded :
    code { bytes := artifactBytes, pos := 13086, limit := 30726 } =
      .ok (Cache.raw.codes[88]!, { bytes := artifactBytes, pos := 13097, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13087, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13090, limit := 13097 })
    (bodyFinish := { bytes := artifactBytes, pos := 13097, limit := 13097 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code88_seq_88_tail0_decoded
  · rfl

#print axioms code88_decoded

@[cbv_eval] theorem code89_seq_89_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13101, limit := 13108 } =
      .ok ((((Cache.raw.codes[89]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13108, limit := 13108 }) := by
  cbv

theorem code89_decoded :
    code { bytes := artifactBytes, pos := 13097, limit := 30726 } =
      .ok (Cache.raw.codes[89]!, { bytes := artifactBytes, pos := 13108, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13098, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13101, limit := 13108 })
    (bodyFinish := { bytes := artifactBytes, pos := 13108, limit := 13108 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code89_seq_89_tail0_decoded
  · rfl

#print axioms code89_decoded

@[cbv_eval] theorem code90_seq_90_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13112, limit := 13119 } =
      .ok ((((Cache.raw.codes[90]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13119, limit := 13119 }) := by
  cbv

theorem code90_decoded :
    code { bytes := artifactBytes, pos := 13108, limit := 30726 } =
      .ok (Cache.raw.codes[90]!, { bytes := artifactBytes, pos := 13119, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13109, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13112, limit := 13119 })
    (bodyFinish := { bytes := artifactBytes, pos := 13119, limit := 13119 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code90_seq_90_tail0_decoded
  · rfl

#print axioms code90_decoded

@[cbv_eval] theorem code91_seq_91_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13123, limit := 13130 } =
      .ok ((((Cache.raw.codes[91]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13130, limit := 13130 }) := by
  cbv

theorem code91_decoded :
    code { bytes := artifactBytes, pos := 13119, limit := 30726 } =
      .ok (Cache.raw.codes[91]!, { bytes := artifactBytes, pos := 13130, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13120, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13123, limit := 13130 })
    (bodyFinish := { bytes := artifactBytes, pos := 13130, limit := 13130 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code91_seq_91_tail0_decoded
  · rfl

#print axioms code91_decoded

@[cbv_eval] theorem code92_seq_92_tail0_decoded :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 13134, limit := 13171 } =
      .ok ((((Cache.raw.codes[92]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13171, limit := 13171 }) := by
  cbv

theorem code92_decoded :
    code { bytes := artifactBytes, pos := 13130, limit := 30726 } =
      .ok (Cache.raw.codes[92]!, { bytes := artifactBytes, pos := 13171, limit := 30726 }) := by
  refine code_eq_of_parts (size := 40)
    (payload := { bytes := artifactBytes, pos := 13131, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13134, limit := 13171 })
    (bodyFinish := { bytes := artifactBytes, pos := 13171, limit := 13171 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code92_seq_92_tail0_decoded
  · rfl

#print axioms code92_decoded

@[cbv_eval] theorem code93_seq_93_43_t_43_t_tail101_decoded :
    instructionSequenceAt 460 true { bytes := artifactBytes, pos := 13599, limit := 13827 } =
      .ok ((((((((Cache.raw.codes[93]!).body)[43]!).childBody false)[43]!).childBody false).drop 101, .otherwise), { bytes := artifactBytes, pos := 13735, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_43_t_43_t_tail49_decoded :
    instructionSequenceAt 512 true { bytes := artifactBytes, pos := 13471, limit := 13827 } =
      .ok ((((((((Cache.raw.codes[93]!).body)[43]!).childBody false)[43]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 13735, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_43_t_43_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 13368, limit := 13827 } =
      .ok ((((((((Cache.raw.codes[93]!).body)[43]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 13735, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_43_t_tail43_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 13366, limit := 13827 } =
      .ok ((((((Cache.raw.codes[93]!).body)[43]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 13775, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_43_t_tail0_decoded :
    instructionSequenceAt 606 true { bytes := artifactBytes, pos := 13272, limit := 13827 } =
      .ok ((((((Cache.raw.codes[93]!).body)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 13775, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_tail43_decoded :
    instructionSequenceAt 608 false { bytes := artifactBytes, pos := 13270, limit := 13827 } =
      .ok ((((Cache.raw.codes[93]!).body).drop 43, .end), { bytes := artifactBytes, pos := 13827, limit := 13827 }) := by
  cbv

@[cbv_eval] theorem code93_seq_93_tail0_decoded :
    instructionSequenceAt 651 false { bytes := artifactBytes, pos := 13176, limit := 13827 } =
      .ok ((((Cache.raw.codes[93]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13827, limit := 13827 }) := by
  cbv

theorem code93_decoded :
    code { bytes := artifactBytes, pos := 13171, limit := 30726 } =
      .ok (Cache.raw.codes[93]!, { bytes := artifactBytes, pos := 13827, limit := 30726 }) := by
  refine code_eq_of_parts (size := 654)
    (payload := { bytes := artifactBytes, pos := 13173, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13176, limit := 13827 })
    (bodyFinish := { bytes := artifactBytes, pos := 13827, limit := 13827 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code93_seq_93_tail0_decoded
  · rfl

#print axioms code93_decoded

@[cbv_eval] theorem code94_seq_94_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13831, limit := 13838 } =
      .ok ((((Cache.raw.codes[94]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13838, limit := 13838 }) := by
  cbv

theorem code94_decoded :
    code { bytes := artifactBytes, pos := 13827, limit := 30726 } =
      .ok (Cache.raw.codes[94]!, { bytes := artifactBytes, pos := 13838, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13828, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13831, limit := 13838 })
    (bodyFinish := { bytes := artifactBytes, pos := 13838, limit := 13838 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code94_seq_94_tail0_decoded
  · rfl

#print axioms code94_decoded

@[cbv_eval] theorem code95_seq_95_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13842, limit := 13849 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13849, limit := 13849 }) := by
  cbv

theorem code95_decoded :
    code { bytes := artifactBytes, pos := 13838, limit := 30726 } =
      .ok (Cache.raw.codes[95]!, { bytes := artifactBytes, pos := 13849, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13839, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13842, limit := 13849 })
    (bodyFinish := { bytes := artifactBytes, pos := 13849, limit := 13849 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code95_seq_95_tail0_decoded
  · rfl

#print axioms code95_decoded


end Project.EulerReconstructed.Artifact
