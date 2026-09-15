import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code64_seq_64_tail0_decoded :
    instructionSequenceAt 41 false { bytes := artifactBytes, pos := 9574, limit := 9615 } =
      .ok ((((Cache.raw.codes[64]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9615, limit := 9615 }) := by
  cbv

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 9570, limit := 30726 } =
      .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 9615, limit := 30726 }) := by
  refine code_eq_of_parts (size := 44)
    (payload := { bytes := artifactBytes, pos := 9571, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9574, limit := 9615 })
    (bodyFinish := { bytes := artifactBytes, pos := 9615, limit := 9615 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code64_seq_64_tail0_decoded
  · rfl

#print axioms code64_decoded

@[cbv_eval] theorem code65_seq_65_tail95_decoded :
    instructionSequenceAt 267 false { bytes := artifactBytes, pos := 9853, limit := 9982 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 95, .end), { bytes := artifactBytes, pos := 9982, limit := 9982 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_tail52_decoded :
    instructionSequenceAt 310 false { bytes := artifactBytes, pos := 9724, limit := 9982 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 52, .end), { bytes := artifactBytes, pos := 9982, limit := 9982 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 9620, limit := 9982 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9982, limit := 9982 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 9615, limit := 30726 } =
      .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 9982, limit := 30726 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 9617, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9620, limit := 9982 })
    (bodyFinish := { bytes := artifactBytes, pos := 9982, limit := 9982 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code65_seq_65_tail0_decoded
  · rfl

#print axioms code65_decoded

@[cbv_eval] theorem code66_seq_66_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 9986, limit := 9993 } =
      .ok ((((Cache.raw.codes[66]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9993, limit := 9993 }) := by
  cbv

theorem code66_decoded :
    code { bytes := artifactBytes, pos := 9982, limit := 30726 } =
      .ok (Cache.raw.codes[66]!, { bytes := artifactBytes, pos := 9993, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 9983, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9986, limit := 9993 })
    (bodyFinish := { bytes := artifactBytes, pos := 9993, limit := 9993 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code66_seq_66_tail0_decoded
  · rfl

#print axioms code66_decoded

@[cbv_eval] theorem code67_seq_67_tail0_decoded :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 9997, limit := 10058 } =
      .ok ((((Cache.raw.codes[67]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10058, limit := 10058 }) := by
  cbv

theorem code67_decoded :
    code { bytes := artifactBytes, pos := 9993, limit := 30726 } =
      .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 10058, limit := 30726 }) := by
  refine code_eq_of_parts (size := 64)
    (payload := { bytes := artifactBytes, pos := 9994, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 9997, limit := 10058 })
    (bodyFinish := { bytes := artifactBytes, pos := 10058, limit := 10058 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code67_seq_67_tail0_decoded
  · rfl

#print axioms code67_decoded

@[cbv_eval] theorem code68_seq_68_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 10062, limit := 10111 } =
      .ok ((((Cache.raw.codes[68]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10111, limit := 10111 }) := by
  cbv

theorem code68_decoded :
    code { bytes := artifactBytes, pos := 10058, limit := 30726 } =
      .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 10111, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 10059, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10062, limit := 10111 })
    (bodyFinish := { bytes := artifactBytes, pos := 10111, limit := 10111 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code68_seq_68_tail0_decoded
  · rfl

#print axioms code68_decoded

@[cbv_eval] theorem code69_seq_69_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 10115, limit := 10164 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10164, limit := 10164 }) := by
  cbv

theorem code69_decoded :
    code { bytes := artifactBytes, pos := 10111, limit := 30726 } =
      .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 10164, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 10112, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10115, limit := 10164 })
    (bodyFinish := { bytes := artifactBytes, pos := 10164, limit := 10164 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code69_seq_69_tail0_decoded
  · rfl

#print axioms code69_decoded

@[cbv_eval] theorem code70_seq_70_tail0_decoded :
    instructionSequenceAt 81 false { bytes := artifactBytes, pos := 10168, limit := 10249 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10249, limit := 10249 }) := by
  cbv

theorem code70_decoded :
    code { bytes := artifactBytes, pos := 10164, limit := 30726 } =
      .ok (Cache.raw.codes[70]!, { bytes := artifactBytes, pos := 10249, limit := 30726 }) := by
  refine code_eq_of_parts (size := 84)
    (payload := { bytes := artifactBytes, pos := 10165, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10168, limit := 10249 })
    (bodyFinish := { bytes := artifactBytes, pos := 10249, limit := 10249 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code70_seq_70_tail0_decoded
  · rfl

#print axioms code70_decoded

@[cbv_eval] theorem code71_seq_71_tail118_decoded :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 10600, limit := 10728 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 118, .end), { bytes := artifactBytes, pos := 10728, limit := 10728 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail109_decoded :
    instructionSequenceAt 365 false { bytes := artifactBytes, pos := 10470, limit := 10728 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 109, .end), { bytes := artifactBytes, pos := 10728, limit := 10728 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail44_decoded :
    instructionSequenceAt 430 false { bytes := artifactBytes, pos := 10342, limit := 10728 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 44, .end), { bytes := artifactBytes, pos := 10728, limit := 10728 }) := by
  cbv

@[cbv_eval] theorem code71_seq_71_tail0_decoded :
    instructionSequenceAt 474 false { bytes := artifactBytes, pos := 10254, limit := 10728 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10728, limit := 10728 }) := by
  cbv

theorem code71_decoded :
    code { bytes := artifactBytes, pos := 10249, limit := 30726 } =
      .ok (Cache.raw.codes[71]!, { bytes := artifactBytes, pos := 10728, limit := 30726 }) := by
  refine code_eq_of_parts (size := 477)
    (payload := { bytes := artifactBytes, pos := 10251, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10254, limit := 10728 })
    (bodyFinish := { bytes := artifactBytes, pos := 10728, limit := 10728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code71_seq_71_tail0_decoded
  · rfl

#print axioms code71_decoded


end Project.EulerReconstructed.Artifact
