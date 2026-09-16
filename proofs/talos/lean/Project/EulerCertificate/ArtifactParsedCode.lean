import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactParsedStates

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem sections_from5 :
    sectionLoop 45631 5 afterExports { bytes := artifactBytes, pos := 2999, limit := 45644 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by
  refine sectionLoop_eq_step (fuel := 45630) (rawId := 10) (id := .code) (rank := 6)
    (payload := { bytes := artifactBytes, pos := 3000, limit := 45644 }) (next := { bytes := artifactBytes, pos := 45644, limit := 45644 })
    (parsed := { afterExports with codes := Cache.raw.codes })
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_code_eq codes_section_decoded
  · exact sections_from6

#print axioms sections_from5

end Project.EulerCertificate.Artifact
