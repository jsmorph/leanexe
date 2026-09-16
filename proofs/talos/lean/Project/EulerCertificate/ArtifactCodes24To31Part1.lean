import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes24To31Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code31_seq_31_tail0_decoded :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 8810, limit := 8848 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8848, limit := 8848 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 8806, limit := 45644 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 8848, limit := 45644 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 8807, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 8810, limit := 8848 })
    (bodyFinish := { bytes := artifactBytes, pos := 8848, limit := 8848 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code31_seq_31_tail0_decoded
  · rfl

#print axioms code31_decoded

end Project.EulerCertificate.Artifact
