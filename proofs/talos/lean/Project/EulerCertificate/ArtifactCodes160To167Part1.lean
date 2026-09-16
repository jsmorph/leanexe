import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes160To167Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code163_seq_163_tail4_decoded :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 33123, limit := 33252 } =
      .ok ((((Cache.raw.codes[163]!).body).drop 4, .end), { bytes := artifactBytes, pos := 33252, limit := 33252 }) := by
  cbv

@[cbv_eval] theorem code163_seq_163_tail0_decoded :
    instructionSequenceAt 142 false { bytes := artifactBytes, pos := 33110, limit := 33252 } =
      .ok ((((Cache.raw.codes[163]!).body).drop 0, .end), { bytes := artifactBytes, pos := 33252, limit := 33252 }) := by
  cbv

theorem code163_decoded :
    code { bytes := artifactBytes, pos := 33105, limit := 45644 } =
      .ok (Cache.raw.codes[163]!, { bytes := artifactBytes, pos := 33252, limit := 45644 }) := by
  refine code_eq_of_parts (size := 145)
    (payload := { bytes := artifactBytes, pos := 33107, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 33110, limit := 33252 })
    (bodyFinish := { bytes := artifactBytes, pos := 33252, limit := 33252 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code163_seq_163_tail0_decoded
  · rfl

#print axioms code163_decoded

@[cbv_eval] theorem code164_seq_164_10_t_tail3_decoded :
    instructionSequenceAt 246 true { bytes := artifactBytes, pos := 33301, limit := 33518 } =
      .ok ((((((Cache.raw.codes[164]!).body)[10]!).childBody false).drop 3, .otherwise), { bytes := artifactBytes, pos := 33490, limit := 33518 }) := by
  cbv

@[cbv_eval] theorem code164_seq_164_10_t_tail0_decoded :
    instructionSequenceAt 249 true { bytes := artifactBytes, pos := 33287, limit := 33518 } =
      .ok ((((((Cache.raw.codes[164]!).body)[10]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 33490, limit := 33518 }) := by
  cbv

@[cbv_eval] theorem code164_seq_164_tail10_decoded :
    instructionSequenceAt 251 false { bytes := artifactBytes, pos := 33285, limit := 33518 } =
      .ok ((((Cache.raw.codes[164]!).body).drop 10, .end), { bytes := artifactBytes, pos := 33518, limit := 33518 }) := by
  cbv

@[cbv_eval] theorem code164_seq_164_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 33257, limit := 33518 } =
      .ok ((((Cache.raw.codes[164]!).body).drop 0, .end), { bytes := artifactBytes, pos := 33518, limit := 33518 }) := by
  cbv

theorem code164_decoded :
    code { bytes := artifactBytes, pos := 33252, limit := 45644 } =
      .ok (Cache.raw.codes[164]!, { bytes := artifactBytes, pos := 33518, limit := 45644 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 33254, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 33257, limit := 33518 })
    (bodyFinish := { bytes := artifactBytes, pos := 33518, limit := 33518 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code164_seq_164_tail0_decoded
  · rfl

#print axioms code164_decoded

@[cbv_eval] theorem code165_seq_165_tail11_decoded :
    instructionSequenceAt 175 false { bytes := artifactBytes, pos := 33574, limit := 33709 } =
      .ok ((((Cache.raw.codes[165]!).body).drop 11, .end), { bytes := artifactBytes, pos := 33709, limit := 33709 }) := by
  cbv

@[cbv_eval] theorem code165_seq_165_tail0_decoded :
    instructionSequenceAt 186 false { bytes := artifactBytes, pos := 33523, limit := 33709 } =
      .ok ((((Cache.raw.codes[165]!).body).drop 0, .end), { bytes := artifactBytes, pos := 33709, limit := 33709 }) := by
  cbv

theorem code165_decoded :
    code { bytes := artifactBytes, pos := 33518, limit := 45644 } =
      .ok (Cache.raw.codes[165]!, { bytes := artifactBytes, pos := 33709, limit := 45644 }) := by
  refine code_eq_of_parts (size := 189)
    (payload := { bytes := artifactBytes, pos := 33520, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 33523, limit := 33709 })
    (bodyFinish := { bytes := artifactBytes, pos := 33709, limit := 33709 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code165_seq_165_tail0_decoded
  · rfl

#print axioms code165_decoded

@[cbv_eval] theorem code166_seq_166_tail128_decoded :
    instructionSequenceAt 268 false { bytes := artifactBytes, pos := 33981, limit := 34110 } =
      .ok ((((Cache.raw.codes[166]!).body).drop 128, .end), { bytes := artifactBytes, pos := 34110, limit := 34110 }) := by
  cbv

@[cbv_eval] theorem code166_seq_166_tail68_decoded :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 33852, limit := 34110 } =
      .ok ((((Cache.raw.codes[166]!).body).drop 68, .end), { bytes := artifactBytes, pos := 34110, limit := 34110 }) := by
  cbv

@[cbv_eval] theorem code166_seq_166_tail5_decoded :
    instructionSequenceAt 391 false { bytes := artifactBytes, pos := 33724, limit := 34110 } =
      .ok ((((Cache.raw.codes[166]!).body).drop 5, .end), { bytes := artifactBytes, pos := 34110, limit := 34110 }) := by
  cbv

@[cbv_eval] theorem code166_seq_166_tail0_decoded :
    instructionSequenceAt 396 false { bytes := artifactBytes, pos := 33714, limit := 34110 } =
      .ok ((((Cache.raw.codes[166]!).body).drop 0, .end), { bytes := artifactBytes, pos := 34110, limit := 34110 }) := by
  cbv

theorem code166_decoded :
    code { bytes := artifactBytes, pos := 33709, limit := 45644 } =
      .ok (Cache.raw.codes[166]!, { bytes := artifactBytes, pos := 34110, limit := 45644 }) := by
  refine code_eq_of_parts (size := 399)
    (payload := { bytes := artifactBytes, pos := 33711, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 33714, limit := 34110 })
    (bodyFinish := { bytes := artifactBytes, pos := 34110, limit := 34110 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code166_seq_166_tail0_decoded
  · rfl

#print axioms code166_decoded

end Project.EulerCertificate.Artifact
