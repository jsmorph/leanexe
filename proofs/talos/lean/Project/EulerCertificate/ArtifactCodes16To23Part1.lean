import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes16To23Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 8086, limit := 45644 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 8165, limit := 45644 }) := by
  refine code_eq_of_parts (size := 78)
    (payload := { bytes := artifactBytes, pos := 8087, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8090, limit := 8165 })
    (bodyFinish := { bytes := artifactBytes, pos := 8165, limit := 8165 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

@[cbv_eval] theorem code23_seq_23_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 8169, limit := 8176 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8176, limit := 8176 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 8165, limit := 45644 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 8176, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 8166, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8169, limit := 8176 })
    (bodyFinish := { bytes := artifactBytes, pos := 8176, limit := 8176 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code23_seq_23_tail0_decoded
  · rfl

#print axioms code23_decoded

end Project.EulerCertificate.Artifact
