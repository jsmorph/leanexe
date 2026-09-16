import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes8To15Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code15_seq_15_tail5_decoded :
    instructionSequenceAt 1342 false { bytes := artifactBytes, pos := 6101, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 5, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

@[cbv_eval] theorem code15_seq_15_tail0_decoded :
    instructionSequenceAt 1347 false { bytes := artifactBytes, pos := 6091, limit := 7438 } =
      .ok ((((Cache.raw.codes[15]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7438, limit := 7438 }) := by
  cbv

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 6086, limit := 45644 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 7438, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1350)
    (payload := { bytes := artifactBytes, pos := 6088, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 6091, limit := 7438 })
    (bodyFinish := { bytes := artifactBytes, pos := 7438, limit := 7438 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code15_seq_15_tail0_decoded
  · rfl

#print axioms code15_decoded

end Project.EulerCertificate.Artifact
