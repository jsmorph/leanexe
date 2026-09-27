import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes120To127Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code126_decoded :
    code { bytes := artifactBytes, pos := 27449, limit := 45644 } =
      .ok (Cache.raw.codes[126]!, { bytes := artifactBytes, pos := 27460, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27450, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27453, limit := 27460 })
    (bodyFinish := { bytes := artifactBytes, pos := 27460, limit := 27460 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code126_seq_126_tail0_decoded
  · rfl

#print axioms code126_decoded

@[cbv_eval] theorem code127_seq_127_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 27464, limit := 27471 } =
      .ok ((((Cache.raw.codes[127]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27471, limit := 27471 }) := by
  cbv

theorem code127_decoded :
    code { bytes := artifactBytes, pos := 27460, limit := 45644 } =
      .ok (Cache.raw.codes[127]!, { bytes := artifactBytes, pos := 27471, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 27461, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 27464, limit := 27471 })
    (bodyFinish := { bytes := artifactBytes, pos := 27471, limit := 27471 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code127_seq_127_tail0_decoded
  · rfl

#print axioms code127_decoded

end Project.EulerCertificate.Artifact
