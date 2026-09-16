import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes80To87Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code86_seq_86_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 20189, limit := 20450 } =
      .ok ((((Cache.raw.codes[86]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20450, limit := 20450 }) := by
  cbv

theorem code86_decoded :
    code { bytes := artifactBytes, pos := 20184, limit := 45644 } =
      .ok (Cache.raw.codes[86]!, { bytes := artifactBytes, pos := 20450, limit := 45644 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 20186, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20189, limit := 20450 })
    (bodyFinish := { bytes := artifactBytes, pos := 20450, limit := 20450 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code86_seq_86_tail0_decoded
  · rfl

#print axioms code86_decoded

@[cbv_eval] theorem code87_seq_87_tail0_decoded :
    instructionSequenceAt 103 false { bytes := artifactBytes, pos := 20454, limit := 20557 } =
      .ok ((((Cache.raw.codes[87]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20557, limit := 20557 }) := by
  cbv

theorem code87_decoded :
    code { bytes := artifactBytes, pos := 20450, limit := 45644 } =
      .ok (Cache.raw.codes[87]!, { bytes := artifactBytes, pos := 20557, limit := 45644 }) := by
  refine code_eq_of_parts (size := 106)
    (payload := { bytes := artifactBytes, pos := 20451, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 20454, limit := 20557 })
    (bodyFinish := { bytes := artifactBytes, pos := 20557, limit := 20557 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code87_seq_87_tail0_decoded
  · rfl

#print axioms code87_decoded

end Project.EulerCertificate.Artifact
