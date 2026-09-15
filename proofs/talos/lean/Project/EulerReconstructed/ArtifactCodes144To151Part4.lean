import Project.EulerReconstructed.ArtifactCodes144To151Part3
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code149_decoded :
    code { bytes := artifactBytes, pos := 29895, limit := 30726 } =
      .ok (Cache.raw.codes[149]!, { bytes := artifactBytes, pos := 30262, limit := 30726 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 29897, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 29900, limit := 30262 })
    (bodyFinish := { bytes := artifactBytes, pos := 30262, limit := 30262 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code149_seq_149_tail0_decoded
  · rfl

#print axioms code149_decoded

@[cbv_eval] theorem code150_seq_150_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 30264, limit := 30290 } =
      .ok ((((Cache.raw.codes[150]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30290, limit := 30290 }) := by
  cbv

theorem code150_decoded :
    code { bytes := artifactBytes, pos := 30262, limit := 30726 } =
      .ok (Cache.raw.codes[150]!, { bytes := artifactBytes, pos := 30290, limit := 30726 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 30263, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 30264, limit := 30290 })
    (bodyFinish := { bytes := artifactBytes, pos := 30290, limit := 30290 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code150_seq_150_tail0_decoded
  · rfl

#print axioms code150_decoded

@[cbv_eval] theorem code151_seq_151_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 30294, limit := 30371 } =
      .ok ((((Cache.raw.codes[151]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30371, limit := 30371 }) := by
  cbv

theorem code151_decoded :
    code { bytes := artifactBytes, pos := 30290, limit := 30726 } =
      .ok (Cache.raw.codes[151]!, { bytes := artifactBytes, pos := 30371, limit := 30726 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 30291, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 30294, limit := 30371 })
    (bodyFinish := { bytes := artifactBytes, pos := 30371, limit := 30371 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code151_seq_151_tail0_decoded
  · rfl

#print axioms code151_decoded
end Project.EulerReconstructed.Artifact
