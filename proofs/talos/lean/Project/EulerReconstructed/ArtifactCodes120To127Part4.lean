import Project.EulerReconstructed.ArtifactCodes120To127Part3
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code127_seq_127_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 19660, limit := 19667 } =
      .ok ((((Cache.raw.codes[127]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19667, limit := 19667 }) := by
  cbv

theorem code127_decoded :
    code { bytes := artifactBytes, pos := 19656, limit := 30726 } =
      .ok (Cache.raw.codes[127]!, { bytes := artifactBytes, pos := 19667, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 19657, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 19660, limit := 19667 })
    (bodyFinish := { bytes := artifactBytes, pos := 19667, limit := 19667 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code127_seq_127_tail0_decoded
  · rfl

#print axioms code127_decoded
end Project.EulerReconstructed.Artifact
