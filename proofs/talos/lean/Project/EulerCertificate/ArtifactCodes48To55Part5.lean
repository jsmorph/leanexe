import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes48To55Part4

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code55_seq_55_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 15445, limit := 15452 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15452, limit := 15452 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 15441, limit := 45644 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 15452, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 15442, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 15445, limit := 15452 })
    (bodyFinish := { bytes := artifactBytes, pos := 15452, limit := 15452 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code55_seq_55_tail0_decoded
  · rfl

#print axioms code55_decoded

end Project.EulerCertificate.Artifact
