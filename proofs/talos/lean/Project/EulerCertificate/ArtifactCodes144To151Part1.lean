import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes144To151Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code149_seq_149_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 30771, limit := 30796 } =
      .ok ((((Cache.raw.codes[149]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30796, limit := 30796 }) := by
  cbv

theorem code149_decoded :
    code { bytes := artifactBytes, pos := 30767, limit := 45644 } =
      .ok (Cache.raw.codes[149]!, { bytes := artifactBytes, pos := 30796, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 30768, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30771, limit := 30796 })
    (bodyFinish := { bytes := artifactBytes, pos := 30796, limit := 30796 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code149_seq_149_tail0_decoded
  · rfl

#print axioms code149_decoded

@[cbv_eval] theorem code150_seq_150_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 30800, limit := 30825 } =
      .ok ((((Cache.raw.codes[150]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30825, limit := 30825 }) := by
  cbv

theorem code150_decoded :
    code { bytes := artifactBytes, pos := 30796, limit := 45644 } =
      .ok (Cache.raw.codes[150]!, { bytes := artifactBytes, pos := 30825, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 30797, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30800, limit := 30825 })
    (bodyFinish := { bytes := artifactBytes, pos := 30825, limit := 30825 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code150_seq_150_tail0_decoded
  · rfl

#print axioms code150_decoded

@[cbv_eval] theorem code151_seq_151_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 30829, limit := 30854 } =
      .ok ((((Cache.raw.codes[151]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30854, limit := 30854 }) := by
  cbv

theorem code151_decoded :
    code { bytes := artifactBytes, pos := 30825, limit := 45644 } =
      .ok (Cache.raw.codes[151]!, { bytes := artifactBytes, pos := 30854, limit := 45644 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 30826, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 30829, limit := 30854 })
    (bodyFinish := { bytes := artifactBytes, pos := 30854, limit := 30854 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code151_seq_151_tail0_decoded
  · rfl

#print axioms code151_decoded

end Project.EulerCertificate.Artifact
