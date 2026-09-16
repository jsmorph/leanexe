import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes176To183Part2

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code183_seq_183_tail0_decoded :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 41442, limit := 41455 } =
      .ok ((((Cache.raw.codes[183]!).body).drop 0, .end), { bytes := artifactBytes, pos := 41455, limit := 41455 }) := by
  cbv

theorem code183_decoded :
    code { bytes := artifactBytes, pos := 41438, limit := 45644 } =
      .ok (Cache.raw.codes[183]!, { bytes := artifactBytes, pos := 41455, limit := 45644 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 41439, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 41442, limit := 41455 })
    (bodyFinish := { bytes := artifactBytes, pos := 41455, limit := 41455 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code183_seq_183_tail0_decoded
  · rfl

#print axioms code183_decoded

end Project.EulerCertificate.Artifact
