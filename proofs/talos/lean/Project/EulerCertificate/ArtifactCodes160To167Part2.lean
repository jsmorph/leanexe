import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes160To167Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code167_seq_167_tail163_decoded :
    instructionSequenceAt 294 false { bytes := artifactBytes, pos := 34444, limit := 34572 } =
      .ok ((((Cache.raw.codes[167]!).body).drop 163, .end), { bytes := artifactBytes, pos := 34572, limit := 34572 }) := by
  cbv

@[cbv_eval] theorem code167_seq_167_tail99_decoded :
    instructionSequenceAt 358 false { bytes := artifactBytes, pos := 34315, limit := 34572 } =
      .ok ((((Cache.raw.codes[167]!).body).drop 99, .end), { bytes := artifactBytes, pos := 34572, limit := 34572 }) := by
  cbv

@[cbv_eval] theorem code167_seq_167_tail35_decoded :
    instructionSequenceAt 422 false { bytes := artifactBytes, pos := 34186, limit := 34572 } =
      .ok ((((Cache.raw.codes[167]!).body).drop 35, .end), { bytes := artifactBytes, pos := 34572, limit := 34572 }) := by
  cbv

@[cbv_eval] theorem code167_seq_167_tail0_decoded :
    instructionSequenceAt 457 false { bytes := artifactBytes, pos := 34115, limit := 34572 } =
      .ok ((((Cache.raw.codes[167]!).body).drop 0, .end), { bytes := artifactBytes, pos := 34572, limit := 34572 }) := by
  cbv

theorem code167_decoded :
    code { bytes := artifactBytes, pos := 34110, limit := 45644 } =
      .ok (Cache.raw.codes[167]!, { bytes := artifactBytes, pos := 34572, limit := 45644 }) := by
  refine code_eq_of_parts (size := 460)
    (payload := { bytes := artifactBytes, pos := 34112, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 34115, limit := 34572 })
    (bodyFinish := { bytes := artifactBytes, pos := 34572, limit := 34572 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code167_seq_167_tail0_decoded
  · rfl

#print axioms code167_decoded

end Project.EulerCertificate.Artifact
