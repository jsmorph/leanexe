import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code80_seq_80_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 12534, limit := 12572 } =
      .ok ((((Cache.raw.codes[80]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12572, limit := 12572 }) := by
  cbv

theorem code80_decoded :
    code { bytes := artifactBytes, pos := 12530, limit := 30726 } =
      .ok (Cache.raw.codes[80]!, { bytes := artifactBytes, pos := 12572, limit := 30726 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 12531, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12534, limit := 12572 })
    (bodyFinish := { bytes := artifactBytes, pos := 12572, limit := 12572 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code80_seq_80_tail0_decoded
  · rfl

#print axioms code80_decoded

@[cbv_eval] theorem code81_seq_81_tail0_decoded :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 12576, limit := 12595 } =
      .ok ((((Cache.raw.codes[81]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12595, limit := 12595 }) := by
  cbv

theorem code81_decoded :
    code { bytes := artifactBytes, pos := 12572, limit := 30726 } =
      .ok (Cache.raw.codes[81]!, { bytes := artifactBytes, pos := 12595, limit := 30726 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 12573, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12576, limit := 12595 })
    (bodyFinish := { bytes := artifactBytes, pos := 12595, limit := 12595 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code81_seq_81_tail0_decoded
  · rfl

#print axioms code81_decoded

@[cbv_eval] theorem code82_seq_82_tail0_decoded :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 12599, limit := 12632 } =
      .ok ((((Cache.raw.codes[82]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12632, limit := 12632 }) := by
  cbv

theorem code82_decoded :
    code { bytes := artifactBytes, pos := 12595, limit := 30726 } =
      .ok (Cache.raw.codes[82]!, { bytes := artifactBytes, pos := 12632, limit := 30726 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 12596, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12599, limit := 12632 })
    (bodyFinish := { bytes := artifactBytes, pos := 12632, limit := 12632 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code82_seq_82_tail0_decoded
  · rfl

#print axioms code82_decoded

@[cbv_eval] theorem code83_seq_83_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 12636, limit := 12649 } =
      .ok ((((Cache.raw.codes[83]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12649, limit := 12649 }) := by
  cbv

theorem code83_decoded :
    code { bytes := artifactBytes, pos := 12632, limit := 30726 } =
      .ok (Cache.raw.codes[83]!, { bytes := artifactBytes, pos := 12649, limit := 30726 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 12633, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12636, limit := 12649 })
    (bodyFinish := { bytes := artifactBytes, pos := 12649, limit := 12649 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code83_seq_83_tail0_decoded
  · rfl

#print axioms code83_decoded

@[cbv_eval] theorem code84_seq_84_18_t_tail49_decoded :
    instructionSequenceAt 288 true { bytes := artifactBytes, pos := 12851, limit := 13011 } =
      .ok ((((((Cache.raw.codes[84]!).body)[18]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 12991, limit := 13011 }) := by
  cbv

@[cbv_eval] theorem code84_seq_84_18_t_tail0_decoded :
    instructionSequenceAt 337 true { bytes := artifactBytes, pos := 12763, limit := 13011 } =
      .ok ((((((Cache.raw.codes[84]!).body)[18]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12991, limit := 13011 }) := by
  cbv

@[cbv_eval] theorem code84_seq_84_tail18_decoded :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 12761, limit := 13011 } =
      .ok ((((Cache.raw.codes[84]!).body).drop 18, .end), { bytes := artifactBytes, pos := 13011, limit := 13011 }) := by
  cbv

@[cbv_eval] theorem code84_seq_84_tail0_decoded :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 12654, limit := 13011 } =
      .ok ((((Cache.raw.codes[84]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13011, limit := 13011 }) := by
  cbv

theorem code84_decoded :
    code { bytes := artifactBytes, pos := 12649, limit := 30726 } =
      .ok (Cache.raw.codes[84]!, { bytes := artifactBytes, pos := 13011, limit := 30726 }) := by
  refine code_eq_of_parts (size := 360)
    (payload := { bytes := artifactBytes, pos := 12651, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12654, limit := 13011 })
    (bodyFinish := { bytes := artifactBytes, pos := 13011, limit := 13011 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code84_seq_84_tail0_decoded
  · rfl

#print axioms code84_decoded

@[cbv_eval] theorem code85_seq_85_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 13015, limit := 13064 } =
      .ok ((((Cache.raw.codes[85]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13064, limit := 13064 }) := by
  cbv

theorem code85_decoded :
    code { bytes := artifactBytes, pos := 13011, limit := 30726 } =
      .ok (Cache.raw.codes[85]!, { bytes := artifactBytes, pos := 13064, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 13012, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13015, limit := 13064 })
    (bodyFinish := { bytes := artifactBytes, pos := 13064, limit := 13064 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code85_seq_85_tail0_decoded
  · rfl

#print axioms code85_decoded

@[cbv_eval] theorem code86_seq_86_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13068, limit := 13075 } =
      .ok ((((Cache.raw.codes[86]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13075, limit := 13075 }) := by
  cbv

theorem code86_decoded :
    code { bytes := artifactBytes, pos := 13064, limit := 30726 } =
      .ok (Cache.raw.codes[86]!, { bytes := artifactBytes, pos := 13075, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13065, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13068, limit := 13075 })
    (bodyFinish := { bytes := artifactBytes, pos := 13075, limit := 13075 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code86_seq_86_tail0_decoded
  · rfl

#print axioms code86_decoded

@[cbv_eval] theorem code87_seq_87_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 13079, limit := 13086 } =
      .ok ((((Cache.raw.codes[87]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13086, limit := 13086 }) := by
  cbv

theorem code87_decoded :
    code { bytes := artifactBytes, pos := 13075, limit := 30726 } =
      .ok (Cache.raw.codes[87]!, { bytes := artifactBytes, pos := 13086, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 13076, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 13079, limit := 13086 })
    (bodyFinish := { bytes := artifactBytes, pos := 13086, limit := 13086 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code87_seq_87_tail0_decoded
  · rfl

#print axioms code87_decoded


end Project.EulerReconstructed.Artifact
