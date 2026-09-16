import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code152_seq_152_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30858, limit := 30865 } =
      .ok ((((Cache.raw.codes[152]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30865, limit := 30865 }) := by
  cbv

theorem code152_decoded :
    code { bytes := artifactBytes, pos := 30854, limit := 45644 } =
      .ok (Cache.raw.codes[152]!, { bytes := artifactBytes, pos := 30865, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30855, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30858, limit := 30865 })
    (bodyFinish := { bytes := artifactBytes, pos := 30865, limit := 30865 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code152_seq_152_tail0_decoded
  · rfl

#print axioms code152_decoded

@[cbv_eval] theorem code153_seq_153_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30869, limit := 30876 } =
      .ok ((((Cache.raw.codes[153]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30876, limit := 30876 }) := by
  cbv

theorem code153_decoded :
    code { bytes := artifactBytes, pos := 30865, limit := 45644 } =
      .ok (Cache.raw.codes[153]!, { bytes := artifactBytes, pos := 30876, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30866, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30869, limit := 30876 })
    (bodyFinish := { bytes := artifactBytes, pos := 30876, limit := 30876 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code153_seq_153_tail0_decoded
  · rfl

#print axioms code153_decoded

@[cbv_eval] theorem code154_seq_154_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30880, limit := 30887 } =
      .ok ((((Cache.raw.codes[154]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30887, limit := 30887 }) := by
  cbv

theorem code154_decoded :
    code { bytes := artifactBytes, pos := 30876, limit := 45644 } =
      .ok (Cache.raw.codes[154]!, { bytes := artifactBytes, pos := 30887, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30877, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30880, limit := 30887 })
    (bodyFinish := { bytes := artifactBytes, pos := 30887, limit := 30887 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code154_seq_154_tail0_decoded
  · rfl

#print axioms code154_decoded

@[cbv_eval] theorem code155_seq_155_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30891, limit := 30898 } =
      .ok ((((Cache.raw.codes[155]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30898, limit := 30898 }) := by
  cbv

theorem code155_decoded :
    code { bytes := artifactBytes, pos := 30887, limit := 45644 } =
      .ok (Cache.raw.codes[155]!, { bytes := artifactBytes, pos := 30898, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30888, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30891, limit := 30898 })
    (bodyFinish := { bytes := artifactBytes, pos := 30898, limit := 30898 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code155_seq_155_tail0_decoded
  · rfl

#print axioms code155_decoded

@[cbv_eval] theorem code156_seq_156_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30902, limit := 30909 } =
      .ok ((((Cache.raw.codes[156]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30909, limit := 30909 }) := by
  cbv

theorem code156_decoded :
    code { bytes := artifactBytes, pos := 30898, limit := 45644 } =
      .ok (Cache.raw.codes[156]!, { bytes := artifactBytes, pos := 30909, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30899, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30902, limit := 30909 })
    (bodyFinish := { bytes := artifactBytes, pos := 30909, limit := 30909 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code156_seq_156_tail0_decoded
  · rfl

#print axioms code156_decoded

@[cbv_eval] theorem code157_seq_157_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 30913, limit := 30920 } =
      .ok ((((Cache.raw.codes[157]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30920, limit := 30920 }) := by
  cbv

theorem code157_decoded :
    code { bytes := artifactBytes, pos := 30909, limit := 45644 } =
      .ok (Cache.raw.codes[157]!, { bytes := artifactBytes, pos := 30920, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 30910, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30913, limit := 30920 })
    (bodyFinish := { bytes := artifactBytes, pos := 30920, limit := 30920 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code157_seq_157_tail0_decoded
  · rfl

#print axioms code157_decoded

@[cbv_eval] theorem code158_seq_158_tail166_decoded :
    instructionSequenceAt 296 false { bytes := artifactBytes, pos := 31258, limit := 31387 } =
      .ok ((((Cache.raw.codes[158]!).body).drop 166, .end), { bytes := artifactBytes, pos := 31387, limit := 31387 }) := by
  cbv

@[cbv_eval] theorem code158_seq_158_tail102_decoded :
    instructionSequenceAt 360 false { bytes := artifactBytes, pos := 31129, limit := 31387 } =
      .ok ((((Cache.raw.codes[158]!).body).drop 102, .end), { bytes := artifactBytes, pos := 31387, limit := 31387 }) := by
  cbv

@[cbv_eval] theorem code158_seq_158_tail38_decoded :
    instructionSequenceAt 424 false { bytes := artifactBytes, pos := 31001, limit := 31387 } =
      .ok ((((Cache.raw.codes[158]!).body).drop 38, .end), { bytes := artifactBytes, pos := 31387, limit := 31387 }) := by
  cbv

@[cbv_eval] theorem code158_seq_158_tail0_decoded :
    instructionSequenceAt 462 false { bytes := artifactBytes, pos := 30925, limit := 31387 } =
      .ok ((((Cache.raw.codes[158]!).body).drop 0, .end), { bytes := artifactBytes, pos := 31387, limit := 31387 }) := by
  cbv

end Project.EulerCertificate.Artifact
