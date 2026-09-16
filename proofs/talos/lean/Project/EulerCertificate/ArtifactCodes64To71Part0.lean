import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code64_seq_64_tail0_decoded :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 15939, limit := 16064 } =
      .ok ((((Cache.raw.codes[64]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16064, limit := 16064 }) := by
  cbv

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 15934, limit := 45644 } =
      .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 16064, limit := 45644 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 15936, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15939, limit := 16064 })
    (bodyFinish := { bytes := artifactBytes, pos := 16064, limit := 16064 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code64_seq_64_tail0_decoded
  · rfl

#print axioms code64_decoded

@[cbv_eval] theorem code65_seq_65_tail11_decoded :
    instructionSequenceAt 170 false { bytes := artifactBytes, pos := 16115, limit := 16250 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 11, .end), { bytes := artifactBytes, pos := 16250, limit := 16250 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_tail0_decoded :
    instructionSequenceAt 181 false { bytes := artifactBytes, pos := 16069, limit := 16250 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16250, limit := 16250 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 16064, limit := 45644 } =
      .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 16250, limit := 45644 }) := by
  refine code_eq_of_parts (size := 184)
    (payload := { bytes := artifactBytes, pos := 16066, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16069, limit := 16250 })
    (bodyFinish := { bytes := artifactBytes, pos := 16250, limit := 16250 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code65_seq_65_tail0_decoded
  · rfl

#print axioms code65_decoded

@[cbv_eval] theorem code66_seq_66_tail60_decoded :
    instructionSequenceAt 189 false { bytes := artifactBytes, pos := 16375, limit := 16504 } =
      .ok ((((Cache.raw.codes[66]!).body).drop 60, .end), { bytes := artifactBytes, pos := 16504, limit := 16504 }) := by
  cbv

@[cbv_eval] theorem code66_seq_66_tail0_decoded :
    instructionSequenceAt 249 false { bytes := artifactBytes, pos := 16255, limit := 16504 } =
      .ok ((((Cache.raw.codes[66]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16504, limit := 16504 }) := by
  cbv

theorem code66_decoded :
    code { bytes := artifactBytes, pos := 16250, limit := 45644 } =
      .ok (Cache.raw.codes[66]!, { bytes := artifactBytes, pos := 16504, limit := 45644 }) := by
  refine code_eq_of_parts (size := 252)
    (payload := { bytes := artifactBytes, pos := 16252, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16255, limit := 16504 })
    (bodyFinish := { bytes := artifactBytes, pos := 16504, limit := 16504 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code66_seq_66_tail0_decoded
  · rfl

#print axioms code66_decoded

@[cbv_eval] theorem code67_seq_67_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 16508, limit := 16581 } =
      .ok ((((Cache.raw.codes[67]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16581, limit := 16581 }) := by
  cbv

theorem code67_decoded :
    code { bytes := artifactBytes, pos := 16504, limit := 45644 } =
      .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 16581, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 16505, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16508, limit := 16581 })
    (bodyFinish := { bytes := artifactBytes, pos := 16581, limit := 16581 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code67_seq_67_tail0_decoded
  · rfl

#print axioms code67_decoded

@[cbv_eval] theorem code68_seq_68_tail0_decoded :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 16585, limit := 16693 } =
      .ok ((((Cache.raw.codes[68]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16693, limit := 16693 }) := by
  cbv

theorem code68_decoded :
    code { bytes := artifactBytes, pos := 16581, limit := 45644 } =
      .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 16693, limit := 45644 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 16582, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16585, limit := 16693 })
    (bodyFinish := { bytes := artifactBytes, pos := 16693, limit := 16693 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code68_seq_68_tail0_decoded
  · rfl

#print axioms code68_decoded

@[cbv_eval] theorem code69_seq_69_tail11_decoded :
    instructionSequenceAt 175 false { bytes := artifactBytes, pos := 16749, limit := 16884 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 11, .end), { bytes := artifactBytes, pos := 16884, limit := 16884 }) := by
  cbv

@[cbv_eval] theorem code69_seq_69_tail0_decoded :
    instructionSequenceAt 186 false { bytes := artifactBytes, pos := 16698, limit := 16884 } =
      .ok ((((Cache.raw.codes[69]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16884, limit := 16884 }) := by
  cbv

theorem code69_decoded :
    code { bytes := artifactBytes, pos := 16693, limit := 45644 } =
      .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 16884, limit := 45644 }) := by
  refine code_eq_of_parts (size := 189)
    (payload := { bytes := artifactBytes, pos := 16695, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16698, limit := 16884 })
    (bodyFinish := { bytes := artifactBytes, pos := 16884, limit := 16884 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code69_seq_69_tail0_decoded
  · rfl

#print axioms code69_decoded

@[cbv_eval] theorem code70_seq_70_tail84_decoded :
    instructionSequenceAt 213 false { bytes := artifactBytes, pos := 17057, limit := 17186 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 84, .end), { bytes := artifactBytes, pos := 17186, limit := 17186 }) := by
  cbv

end Project.EulerCertificate.Artifact
