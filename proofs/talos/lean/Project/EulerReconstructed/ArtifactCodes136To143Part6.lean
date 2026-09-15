import Project.EulerReconstructed.ArtifactCodes136To143Part5
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code142_seq_142_tail0_decoded :
    instructionSequenceAt 525 false { bytes := artifactBytes, pos := 26444, limit := 26969 } =
      .ok ((((Cache.raw.codes[142]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26969, limit := 26969 }) := by
  cbv

theorem code142_decoded :
    code { bytes := artifactBytes, pos := 26439, limit := 30726 } =
      .ok (Cache.raw.codes[142]!, { bytes := artifactBytes, pos := 26969, limit := 30726 }) := by
  refine code_eq_of_parts (size := 528)
    (payload := { bytes := artifactBytes, pos := 26441, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 26444, limit := 26969 })
    (bodyFinish := { bytes := artifactBytes, pos := 26969, limit := 26969 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code142_seq_142_tail0_decoded
  · rfl

#print axioms code142_decoded

@[cbv_eval] theorem code143_seq_143_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 26973, limit := 26980 } =
      .ok ((((Cache.raw.codes[143]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26980, limit := 26980 }) := by
  cbv

theorem code143_decoded :
    code { bytes := artifactBytes, pos := 26969, limit := 30726 } =
      .ok (Cache.raw.codes[143]!, { bytes := artifactBytes, pos := 26980, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 26970, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 26973, limit := 26980 })
    (bodyFinish := { bytes := artifactBytes, pos := 26980, limit := 26980 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code143_seq_143_tail0_decoded
  · rfl

#print axioms code143_decoded
end Project.EulerReconstructed.Artifact
