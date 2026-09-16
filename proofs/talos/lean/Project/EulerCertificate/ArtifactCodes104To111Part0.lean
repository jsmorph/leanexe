import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code104_seq_104_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 23983, limit := 24008 } =
      .ok ((((Cache.raw.codes[104]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24008, limit := 24008 }) := by
  cbv

theorem code104_decoded :
    code { bytes := artifactBytes, pos := 23979, limit := 45644 } =
      .ok (Cache.raw.codes[104]!, { bytes := artifactBytes, pos := 24008, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 23980, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 23983, limit := 24008 })
    (bodyFinish := { bytes := artifactBytes, pos := 24008, limit := 24008 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code104_seq_104_tail0_decoded
  · rfl

#print axioms code104_decoded

@[cbv_eval] theorem code105_seq_105_tail0_decoded :
    instructionSequenceAt 41 false { bytes := artifactBytes, pos := 24012, limit := 24053 } =
      .ok ((((Cache.raw.codes[105]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24053, limit := 24053 }) := by
  cbv

theorem code105_decoded :
    code { bytes := artifactBytes, pos := 24008, limit := 45644 } =
      .ok (Cache.raw.codes[105]!, { bytes := artifactBytes, pos := 24053, limit := 45644 }) := by
  refine code_eq_of_parts (size := 44)
    (payload := { bytes := artifactBytes, pos := 24009, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24012, limit := 24053 })
    (bodyFinish := { bytes := artifactBytes, pos := 24053, limit := 24053 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code105_seq_105_tail0_decoded
  · rfl

#print axioms code105_decoded

@[cbv_eval] theorem code106_seq_106_tail95_decoded :
    instructionSequenceAt 267 false { bytes := artifactBytes, pos := 24291, limit := 24420 } =
      .ok ((((Cache.raw.codes[106]!).body).drop 95, .end), { bytes := artifactBytes, pos := 24420, limit := 24420 }) := by
  cbv

@[cbv_eval] theorem code106_seq_106_tail52_decoded :
    instructionSequenceAt 310 false { bytes := artifactBytes, pos := 24162, limit := 24420 } =
      .ok ((((Cache.raw.codes[106]!).body).drop 52, .end), { bytes := artifactBytes, pos := 24420, limit := 24420 }) := by
  cbv

@[cbv_eval] theorem code106_seq_106_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 24058, limit := 24420 } =
      .ok ((((Cache.raw.codes[106]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24420, limit := 24420 }) := by
  cbv

theorem code106_decoded :
    code { bytes := artifactBytes, pos := 24053, limit := 45644 } =
      .ok (Cache.raw.codes[106]!, { bytes := artifactBytes, pos := 24420, limit := 45644 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 24055, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24058, limit := 24420 })
    (bodyFinish := { bytes := artifactBytes, pos := 24420, limit := 24420 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code106_seq_106_tail0_decoded
  · rfl

#print axioms code106_decoded

@[cbv_eval] theorem code107_seq_107_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 24424, limit := 24431 } =
      .ok ((((Cache.raw.codes[107]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24431, limit := 24431 }) := by
  cbv

theorem code107_decoded :
    code { bytes := artifactBytes, pos := 24420, limit := 45644 } =
      .ok (Cache.raw.codes[107]!, { bytes := artifactBytes, pos := 24431, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 24421, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24424, limit := 24431 })
    (bodyFinish := { bytes := artifactBytes, pos := 24431, limit := 24431 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code107_seq_107_tail0_decoded
  · rfl

#print axioms code107_decoded

@[cbv_eval] theorem code108_seq_108_tail0_decoded :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 24435, limit := 24496 } =
      .ok ((((Cache.raw.codes[108]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24496, limit := 24496 }) := by
  cbv

theorem code108_decoded :
    code { bytes := artifactBytes, pos := 24431, limit := 45644 } =
      .ok (Cache.raw.codes[108]!, { bytes := artifactBytes, pos := 24496, limit := 45644 }) := by
  refine code_eq_of_parts (size := 64)
    (payload := { bytes := artifactBytes, pos := 24432, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24435, limit := 24496 })
    (bodyFinish := { bytes := artifactBytes, pos := 24496, limit := 24496 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code108_seq_108_tail0_decoded
  · rfl

#print axioms code108_decoded

@[cbv_eval] theorem code109_seq_109_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 24500, limit := 24549 } =
      .ok ((((Cache.raw.codes[109]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24549, limit := 24549 }) := by
  cbv

theorem code109_decoded :
    code { bytes := artifactBytes, pos := 24496, limit := 45644 } =
      .ok (Cache.raw.codes[109]!, { bytes := artifactBytes, pos := 24549, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 24497, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24500, limit := 24549 })
    (bodyFinish := { bytes := artifactBytes, pos := 24549, limit := 24549 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code109_seq_109_tail0_decoded
  · rfl

#print axioms code109_decoded

@[cbv_eval] theorem code110_seq_110_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 24553, limit := 24602 } =
      .ok ((((Cache.raw.codes[110]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24602, limit := 24602 }) := by
  cbv

theorem code110_decoded :
    code { bytes := artifactBytes, pos := 24549, limit := 45644 } =
      .ok (Cache.raw.codes[110]!, { bytes := artifactBytes, pos := 24602, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 24550, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24553, limit := 24602 })
    (bodyFinish := { bytes := artifactBytes, pos := 24602, limit := 24602 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code110_seq_110_tail0_decoded
  · rfl

#print axioms code110_decoded

end Project.EulerCertificate.Artifact
