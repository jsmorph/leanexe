import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes48To55Part3

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code53_seq_53_4_e_28_t_tail0_decoded :
    instructionSequenceAt 1046 true { bytes := artifactBytes, pos := 15051, limit := 15232 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[4]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15195, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_tail113_decoded :
    instructionSequenceAt 963 true { bytes := artifactBytes, pos := 14706, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody false).drop 113, .otherwise), { bytes := artifactBytes, pos := 14834, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_tail55_decoded :
    instructionSequenceAt 1021 true { bytes := artifactBytes, pos := 14459, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody false).drop 55, .otherwise), { bytes := artifactBytes, pos := 14834, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_tail51_decoded :
    instructionSequenceAt 1025 true { bytes := artifactBytes, pos := 14290, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody false).drop 51, .otherwise), { bytes := artifactBytes, pos := 14834, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_t_tail0_decoded :
    instructionSequenceAt 1076 true { bytes := artifactBytes, pos := 14169, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14834, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_tail28_decoded :
    instructionSequenceAt 1048 false { bytes := artifactBytes, pos := 15049, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 15227, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_tail24_decoded :
    instructionSequenceAt 1052 false { bytes := artifactBytes, pos := 14880, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody true).drop 24, .end), { bytes := artifactBytes, pos := 15227, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_4_e_tail0_decoded :
    instructionSequenceAt 1076 false { bytes := artifactBytes, pos := 14834, limit := 15232 } =
      .ok ((((((Cache.raw.codes[53]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 15227, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_tail4_decoded :
    instructionSequenceAt 1078 false { bytes := artifactBytes, pos := 14167, limit := 15232 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 4, .end), { bytes := artifactBytes, pos := 15232, limit := 15232 }) := by
  cbv

@[cbv_eval] theorem code53_seq_53_tail0_decoded :
    instructionSequenceAt 1082 false { bytes := artifactBytes, pos := 14150, limit := 15232 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15232, limit := 15232 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 14145, limit := 45644 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 15232, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1085)
    (payload := { bytes := artifactBytes, pos := 14147, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 14150, limit := 15232 })
    (bodyFinish := { bytes := artifactBytes, pos := 15232, limit := 15232 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code53_seq_53_tail0_decoded
  · rfl

#print axioms code53_decoded

@[cbv_eval] theorem code54_seq_54_7_e_tail3_decoded :
    instructionSequenceAt 192 false { bytes := artifactBytes, pos := 15266, limit := 15441 } =
      .ok ((((((Cache.raw.codes[54]!).body)[7]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 15438, limit := 15441 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_7_e_tail0_decoded :
    instructionSequenceAt 195 false { bytes := artifactBytes, pos := 15261, limit := 15441 } =
      .ok ((((((Cache.raw.codes[54]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 15438, limit := 15441 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail7_decoded :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 15254, limit := 15441 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 7, .end), { bytes := artifactBytes, pos := 15441, limit := 15441 }) := by
  cbv

@[cbv_eval] theorem code54_seq_54_tail0_decoded :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 15237, limit := 15441 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15441, limit := 15441 }) := by
  cbv

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 15232, limit := 45644 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 15441, limit := 45644 }) := by
  refine code_eq_of_parts (size := 207)
    (payload := { bytes := artifactBytes, pos := 15234, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15237, limit := 15441 })
    (bodyFinish := { bytes := artifactBytes, pos := 15441, limit := 15441 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code54_seq_54_tail0_decoded
  · rfl

#print axioms code54_decoded

end Project.EulerCertificate.Artifact
