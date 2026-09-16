import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes0To7Part2

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code3_seq_3_tail82_decoded :
    instructionSequenceAt 2702 false { bytes := artifactBytes, pos := 3705, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 82, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail47_decoded :
    instructionSequenceAt 2737 false { bytes := artifactBytes, pos := 3457, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 47, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail34_decoded :
    instructionSequenceAt 2750 false { bytes := artifactBytes, pos := 3288, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 34, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail30_decoded :
    instructionSequenceAt 2754 false { bytes := artifactBytes, pos := 3119, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 30, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

@[cbv_eval] theorem code3_seq_3_tail0_decoded :
    instructionSequenceAt 2784 false { bytes := artifactBytes, pos := 3061, limit := 5845 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5845, limit := 5845 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 3056, limit := 45644 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 5845, limit := 45644 }) := by
  refine code_eq_of_parts (size := 2787)
    (payload := { bytes := artifactBytes, pos := 3058, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 3061, limit := 5845 })
    (bodyFinish := { bytes := artifactBytes, pos := 5845, limit := 5845 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code3_seq_3_tail0_decoded
  · rfl

#print axioms code3_decoded

@[cbv_eval] theorem code4_seq_4_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5849, limit := 5856 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5856, limit := 5856 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 5845, limit := 45644 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 5856, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5846, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5849, limit := 5856 })
    (bodyFinish := { bytes := artifactBytes, pos := 5856, limit := 5856 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code4_seq_4_tail0_decoded
  · rfl

#print axioms code4_decoded

@[cbv_eval] theorem code5_seq_5_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5860, limit := 5867 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5867, limit := 5867 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 5856, limit := 45644 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 5867, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5857, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5860, limit := 5867 })
    (bodyFinish := { bytes := artifactBytes, pos := 5867, limit := 5867 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code5_seq_5_tail0_decoded
  · rfl

#print axioms code5_decoded

@[cbv_eval] theorem code6_seq_6_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 5871, limit := 5884 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5884, limit := 5884 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 5867, limit := 45644 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 5884, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 5868, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5871, limit := 5884 })
    (bodyFinish := { bytes := artifactBytes, pos := 5884, limit := 5884 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code6_seq_6_tail0_decoded
  · rfl

#print axioms code6_decoded

@[cbv_eval] theorem code7_seq_7_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 5888, limit := 5961 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5961, limit := 5961 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 5884, limit := 45644 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 5961, limit := 45644 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 5885, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 5888, limit := 5961 })
    (bodyFinish := { bytes := artifactBytes, pos := 5961, limit := 5961 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code7_seq_7_tail0_decoded
  · rfl

#print axioms code7_decoded

end Project.EulerCertificate.Artifact
