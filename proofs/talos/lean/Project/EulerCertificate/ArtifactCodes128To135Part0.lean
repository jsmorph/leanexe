import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code128_seq_128_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27475, limit := 27482 } =
      .ok ((((Cache.raw.codes[128]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27482, limit := 27482 }) := by
  cbv

theorem code128_decoded :
    code { bytes := artifactBytes, pos := 27471, limit := 45644 } =
      .ok (Cache.raw.codes[128]!, { bytes := artifactBytes, pos := 27482, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27472, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27475, limit := 27482 })
    (bodyFinish := { bytes := artifactBytes, pos := 27482, limit := 27482 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code128_seq_128_tail0_decoded
  · rfl

#print axioms code128_decoded

@[cbv_eval] theorem code129_seq_129_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27486, limit := 27493 } =
      .ok ((((Cache.raw.codes[129]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27493, limit := 27493 }) := by
  cbv

theorem code129_decoded :
    code { bytes := artifactBytes, pos := 27482, limit := 45644 } =
      .ok (Cache.raw.codes[129]!, { bytes := artifactBytes, pos := 27493, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27483, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27486, limit := 27493 })
    (bodyFinish := { bytes := artifactBytes, pos := 27493, limit := 27493 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code129_seq_129_tail0_decoded
  · rfl

#print axioms code129_decoded

@[cbv_eval] theorem code130_seq_130_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27497, limit := 27504 } =
      .ok ((((Cache.raw.codes[130]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27504, limit := 27504 }) := by
  cbv

theorem code130_decoded :
    code { bytes := artifactBytes, pos := 27493, limit := 45644 } =
      .ok (Cache.raw.codes[130]!, { bytes := artifactBytes, pos := 27504, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27494, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27497, limit := 27504 })
    (bodyFinish := { bytes := artifactBytes, pos := 27504, limit := 27504 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code130_seq_130_tail0_decoded
  · rfl

#print axioms code130_decoded

@[cbv_eval] theorem code131_seq_131_tail0_decoded :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 27508, limit := 27545 } =
      .ok ((((Cache.raw.codes[131]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27545, limit := 27545 }) := by
  cbv

theorem code131_decoded :
    code { bytes := artifactBytes, pos := 27504, limit := 45644 } =
      .ok (Cache.raw.codes[131]!, { bytes := artifactBytes, pos := 27545, limit := 45644 }) := by
  refine code_eq_of_parts (size := 40)
    (payload := { bytes := artifactBytes, pos := 27505, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27508, limit := 27545 })
    (bodyFinish := { bytes := artifactBytes, pos := 27545, limit := 27545 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code131_seq_131_tail0_decoded
  · rfl

#print axioms code131_decoded

@[cbv_eval] theorem code132_seq_132_43_t_43_t_tail101_decoded :
    instructionSequenceAt 463 true { bytes := artifactBytes, pos := 27973, limit := 28204 } =
      .ok ((((((((Cache.raw.codes[132]!).body)[43]!).childBody false)[43]!).childBody false).drop 101, .otherwise), { bytes := artifactBytes, pos := 28110, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_43_t_43_t_tail49_decoded :
    instructionSequenceAt 515 true { bytes := artifactBytes, pos := 27845, limit := 28204 } =
      .ok ((((((((Cache.raw.codes[132]!).body)[43]!).childBody false)[43]!).childBody false).drop 49, .otherwise), { bytes := artifactBytes, pos := 28110, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_43_t_43_t_tail0_decoded :
    instructionSequenceAt 564 true { bytes := artifactBytes, pos := 27742, limit := 28204 } =
      .ok ((((((((Cache.raw.codes[132]!).body)[43]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 28110, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_43_t_tail43_decoded :
    instructionSequenceAt 566 true { bytes := artifactBytes, pos := 27740, limit := 28204 } =
      .ok ((((((Cache.raw.codes[132]!).body)[43]!).childBody false).drop 43, .otherwise), { bytes := artifactBytes, pos := 28151, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_43_t_tail0_decoded :
    instructionSequenceAt 609 true { bytes := artifactBytes, pos := 27646, limit := 28204 } =
      .ok ((((((Cache.raw.codes[132]!).body)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 28151, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_tail43_decoded :
    instructionSequenceAt 611 false { bytes := artifactBytes, pos := 27644, limit := 28204 } =
      .ok ((((Cache.raw.codes[132]!).body).drop 43, .end), { bytes := artifactBytes, pos := 28204, limit := 28204 }) := by
  cbv

@[cbv_eval] theorem code132_seq_132_tail0_decoded :
    instructionSequenceAt 654 false { bytes := artifactBytes, pos := 27550, limit := 28204 } =
      .ok ((((Cache.raw.codes[132]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28204, limit := 28204 }) := by
  cbv

theorem code132_decoded :
    code { bytes := artifactBytes, pos := 27545, limit := 45644 } =
      .ok (Cache.raw.codes[132]!, { bytes := artifactBytes, pos := 28204, limit := 45644 }) := by
  refine code_eq_of_parts (size := 657)
    (payload := { bytes := artifactBytes, pos := 27547, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27550, limit := 28204 })
    (bodyFinish := { bytes := artifactBytes, pos := 28204, limit := 28204 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code132_seq_132_tail0_decoded
  · rfl

#print axioms code132_decoded

end Project.EulerCertificate.Artifact
