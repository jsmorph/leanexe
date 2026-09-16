import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code80_seq_80_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 19381, limit := 19489 } =
      .ok ((((Cache.raw.codes[80]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19489, limit := 19489 }) := by
  cbv

theorem code80_decoded :
    code { bytes := artifactBytes, pos := 19377, limit := 45644 } =
      .ok (Cache.raw.codes[80]!, { bytes := artifactBytes, pos := 19489, limit := 45644 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 19378, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19381, limit := 19489 })
    (bodyFinish := { bytes := artifactBytes, pos := 19489, limit := 19489 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code80_seq_80_tail0_decoded
  · rfl

#print axioms code80_decoded

@[cbv_eval] theorem code81_seq_81_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 19493, limit := 19608 } =
      .ok ((((Cache.raw.codes[81]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19608, limit := 19608 }) := by
  cbv

theorem code81_decoded :
    code { bytes := artifactBytes, pos := 19489, limit := 45644 } =
      .ok (Cache.raw.codes[81]!, { bytes := artifactBytes, pos := 19608, limit := 45644 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 19490, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19493, limit := 19608 })
    (bodyFinish := { bytes := artifactBytes, pos := 19608, limit := 19608 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code81_seq_81_tail0_decoded
  · rfl

#print axioms code81_decoded

@[cbv_eval] theorem code82_seq_82_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 19613, limit := 19742 } =
      .ok ((((Cache.raw.codes[82]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19742, limit := 19742 }) := by
  cbv

theorem code82_decoded :
    code { bytes := artifactBytes, pos := 19608, limit := 45644 } =
      .ok (Cache.raw.codes[82]!, { bytes := artifactBytes, pos := 19742, limit := 45644 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 19610, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19613, limit := 19742 })
    (bodyFinish := { bytes := artifactBytes, pos := 19742, limit := 19742 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code82_seq_82_tail0_decoded
  · rfl

#print axioms code82_decoded

@[cbv_eval] theorem code83_seq_83_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 19813, limit := 19954 } =
      .ok ((((Cache.raw.codes[83]!).body).drop 29, .end), { bytes := artifactBytes, pos := 19954, limit := 19954 }) := by
  cbv

@[cbv_eval] theorem code83_seq_83_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 19747, limit := 19954 } =
      .ok ((((Cache.raw.codes[83]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19954, limit := 19954 }) := by
  cbv

theorem code83_decoded :
    code { bytes := artifactBytes, pos := 19742, limit := 45644 } =
      .ok (Cache.raw.codes[83]!, { bytes := artifactBytes, pos := 19954, limit := 45644 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 19744, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19747, limit := 19954 })
    (bodyFinish := { bytes := artifactBytes, pos := 19954, limit := 19954 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code83_seq_83_tail0_decoded
  · rfl

#print axioms code83_decoded

@[cbv_eval] theorem code84_seq_84_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 19958, limit := 20065 } =
      .ok ((((Cache.raw.codes[84]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20065, limit := 20065 }) := by
  cbv

theorem code84_decoded :
    code { bytes := artifactBytes, pos := 19954, limit := 45644 } =
      .ok (Cache.raw.codes[84]!, { bytes := artifactBytes, pos := 20065, limit := 45644 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 19955, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 19958, limit := 20065 })
    (bodyFinish := { bytes := artifactBytes, pos := 20065, limit := 20065 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code84_seq_84_tail0_decoded
  · rfl

#print axioms code84_decoded

@[cbv_eval] theorem code85_seq_85_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 20069, limit := 20184 } =
      .ok ((((Cache.raw.codes[85]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20184, limit := 20184 }) := by
  cbv

theorem code85_decoded :
    code { bytes := artifactBytes, pos := 20065, limit := 45644 } =
      .ok (Cache.raw.codes[85]!, { bytes := artifactBytes, pos := 20184, limit := 45644 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 20066, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20069, limit := 20184 })
    (bodyFinish := { bytes := artifactBytes, pos := 20184, limit := 20184 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code85_seq_85_tail0_decoded
  · rfl

#print axioms code85_decoded

@[cbv_eval] theorem code86_seq_86_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 20302, limit := 20450 } =
      .ok ((((((Cache.raw.codes[86]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 20430, limit := 20450 }) := by
  cbv

@[cbv_eval] theorem code86_seq_86_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 20236, limit := 20450 } =
      .ok ((((((Cache.raw.codes[86]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 20430, limit := 20450 }) := by
  cbv

@[cbv_eval] theorem code86_seq_86_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 20234, limit := 20450 } =
      .ok ((((Cache.raw.codes[86]!).body).drop 21, .end), { bytes := artifactBytes, pos := 20450, limit := 20450 }) := by
  cbv

end Project.EulerCertificate.Artifact
