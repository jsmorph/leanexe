import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes88To95Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code94_seq_94_16_t_tail26_decoded :
    instructionSequenceAt 245 true { bytes := artifactBytes, pos := 21345, limit := 21501 } =
      .ok ((((((Cache.raw.codes[94]!).body)[16]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 21481, limit := 21501 }) := by
  cbv

@[cbv_eval] theorem code94_seq_94_16_t_tail0_decoded :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 21285, limit := 21501 } =
      .ok ((((((Cache.raw.codes[94]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 21481, limit := 21501 }) := by
  cbv

@[cbv_eval] theorem code94_seq_94_tail16_decoded :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 21283, limit := 21501 } =
      .ok ((((Cache.raw.codes[94]!).body).drop 16, .end), { bytes := artifactBytes, pos := 21501, limit := 21501 }) := by
  cbv

@[cbv_eval] theorem code94_seq_94_tail0_decoded :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 21212, limit := 21501 } =
      .ok ((((Cache.raw.codes[94]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21501, limit := 21501 }) := by
  cbv

theorem code94_decoded :
    code { bytes := artifactBytes, pos := 21207, limit := 45644 } =
      .ok (Cache.raw.codes[94]!, { bytes := artifactBytes, pos := 21501, limit := 45644 }) := by
  refine code_eq_of_parts (size := 292)
    (payload := { bytes := artifactBytes, pos := 21209, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21212, limit := 21501 })
    (bodyFinish := { bytes := artifactBytes, pos := 21501, limit := 21501 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code94_seq_94_tail0_decoded
  · rfl

#print axioms code94_decoded

@[cbv_eval] theorem code95_seq_95_tail3_decoded :
    instructionSequenceAt 135 false { bytes := artifactBytes, pos := 21511, limit := 21644 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 3, .end), { bytes := artifactBytes, pos := 21644, limit := 21644 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_tail0_decoded :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 21506, limit := 21644 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21644, limit := 21644 }) := by
  cbv

theorem code95_decoded :
    code { bytes := artifactBytes, pos := 21501, limit := 45644 } =
      .ok (Cache.raw.codes[95]!, { bytes := artifactBytes, pos := 21644, limit := 45644 }) := by
  refine code_eq_of_parts (size := 141)
    (payload := { bytes := artifactBytes, pos := 21503, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 21506, limit := 21644 })
    (bodyFinish := { bytes := artifactBytes, pos := 21644, limit := 21644 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code95_seq_95_tail0_decoded
  · rfl

#print axioms code95_decoded

end Project.EulerCertificate.Artifact
