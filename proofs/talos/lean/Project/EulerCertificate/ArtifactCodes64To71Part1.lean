import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes64To71Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code70_seq_70_tail20_decoded :
    instructionSequenceAt 277 false { bytes := artifactBytes, pos := 16929, limit := 17186 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 20, .end), { bytes := artifactBytes, pos := 17186, limit := 17186 }) := by
  cbv

@[cbv_eval] theorem code70_seq_70_tail0_decoded :
    instructionSequenceAt 297 false { bytes := artifactBytes, pos := 16889, limit := 17186 } =
      .ok ((((Cache.raw.codes[70]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17186, limit := 17186 }) := by
  cbv

theorem code70_decoded :
    code { bytes := artifactBytes, pos := 16884, limit := 45644 } =
      .ok (Cache.raw.codes[70]!, { bytes := artifactBytes, pos := 17186, limit := 45644 }) := by
  refine code_eq_of_parts (size := 300)
    (payload := { bytes := artifactBytes, pos := 16886, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 16889, limit := 17186 })
    (bodyFinish := { bytes := artifactBytes, pos := 17186, limit := 17186 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code70_seq_70_tail0_decoded
  · rfl

#print axioms code70_decoded

@[cbv_eval] theorem code71_seq_71_tail0_decoded :
    instructionSequenceAt 70 false { bytes := artifactBytes, pos := 17190, limit := 17260 } =
      .ok ((((Cache.raw.codes[71]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17260, limit := 17260 }) := by
  cbv

theorem code71_decoded :
    code { bytes := artifactBytes, pos := 17186, limit := 45644 } =
      .ok (Cache.raw.codes[71]!, { bytes := artifactBytes, pos := 17260, limit := 45644 }) := by
  refine code_eq_of_parts (size := 73)
    (payload := { bytes := artifactBytes, pos := 17187, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 17190, limit := 17260 })
    (bodyFinish := { bytes := artifactBytes, pos := 17260, limit := 17260 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code71_seq_71_tail0_decoded
  · rfl

#print axioms code71_decoded

end Project.EulerCertificate.Artifact
