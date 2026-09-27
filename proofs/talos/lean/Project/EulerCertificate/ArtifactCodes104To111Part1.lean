import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes104To111Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code111_seq_111_tail0_decoded :
    instructionSequenceAt 81 false { bytes := artifactBytes, pos := 24606, limit := 24687 } =
      .ok ((((Cache.raw.codes[111]!).body).drop 0, .end), { bytes := artifactBytes, pos := 24687, limit := 24687 }) := by
  cbv

theorem code111_decoded :
    code { bytes := artifactBytes, pos := 24602, limit := 45644 } =
      .ok (Cache.raw.codes[111]!, { bytes := artifactBytes, pos := 24687, limit := 45644 }) := by
  refine code_eq_of_parts (size := 84)
    (payload := { bytes := artifactBytes, pos := 24603, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 24606, limit := 24687 })
    (bodyFinish := { bytes := artifactBytes, pos := 24687, limit := 24687 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code111_seq_111_tail0_decoded
  · rfl

#print axioms code111_decoded

end Project.EulerCertificate.Artifact
