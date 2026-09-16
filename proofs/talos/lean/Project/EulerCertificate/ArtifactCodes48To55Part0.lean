import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code48_seq_48_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 10955, limit := 10962 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10962, limit := 10962 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 10951, limit := 45644 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 10962, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 10952, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 10955, limit := 10962 })
    (bodyFinish := { bytes := artifactBytes, pos := 10962, limit := 10962 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_seq_48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_seq_49_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 10966, limit := 10973 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10973, limit := 10973 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 10962, limit := 45644 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 10973, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 10963, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 10966, limit := 10973 })
    (bodyFinish := { bytes := artifactBytes, pos := 10973, limit := 10973 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_seq_49_tail0_decoded
  · rfl

#print axioms code49_decoded

@[cbv_eval] theorem code50_seq_50_tail67_decoded :
    instructionSequenceAt 550 false { bytes := artifactBytes, pos := 11466, limit := 11595 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 67, .end), { bytes := artifactBytes, pos := 11595, limit := 11595 }) := by
  cbv

@[cbv_eval] theorem code50_seq_50_tail62_decoded :
    instructionSequenceAt 555 false { bytes := artifactBytes, pos := 11328, limit := 11595 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 62, .end), { bytes := artifactBytes, pos := 11595, limit := 11595 }) := by
  cbv

@[cbv_eval] theorem code50_seq_50_tail31_decoded :
    instructionSequenceAt 586 false { bytes := artifactBytes, pos := 11097, limit := 11595 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 31, .end), { bytes := artifactBytes, pos := 11595, limit := 11595 }) := by
  cbv

@[cbv_eval] theorem code50_seq_50_tail0_decoded :
    instructionSequenceAt 617 false { bytes := artifactBytes, pos := 10978, limit := 11595 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11595, limit := 11595 }) := by
  cbv

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 10973, limit := 45644 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 11595, limit := 45644 }) := by
  refine code_eq_of_parts (size := 620)
    (payload := { bytes := artifactBytes, pos := 10975, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 10978, limit := 11595 })
    (bodyFinish := { bytes := artifactBytes, pos := 11595, limit := 11595 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code50_seq_50_tail0_decoded
  · rfl

#print axioms code50_decoded

@[cbv_eval] theorem code51_seq_51_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 11599, limit := 11606 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11606, limit := 11606 }) := by
  cbv

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 11595, limit := 45644 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 11606, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 11596, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 11599, limit := 11606 })
    (bodyFinish := { bytes := artifactBytes, pos := 11606, limit := 11606 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code51_seq_51_tail0_decoded
  · rfl

#print axioms code51_decoded

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_52_t_0_t_tail18_decoded :
    instructionSequenceAt 2436 false { bytes := artifactBytes, pos := 11806, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 11934, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_t_52_t_0_t_tail0_decoded :
    instructionSequenceAt 2454 false { bytes := artifactBytes, pos := 11775, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false)[52]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11934, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_36_t_0_t_tail18_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 12286, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 12414, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_36_t_0_t_tail0_decoded :
    instructionSequenceAt 2470 false { bytes := artifactBytes, pos := 12255, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12414, limit := 14145 }) := by
  cbv

@[cbv_eval] theorem code52_seq_52_4_t_0_t_14_e_53_t_0_t_tail139_decoded :
    instructionSequenceAt 2314 false { bytes := artifactBytes, pos := 12841, limit := 14145 } =
      .ok ((((((((((((((Cache.raw.codes[52]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 139, .end), { bytes := artifactBytes, pos := 12969, limit := 14145 }) := by
  cbv

end Project.EulerCertificate.Artifact
