import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_tail0 :
    instructionSequenceAt 103 false { bytes := artifactBytes, pos := 4356, limit := 4459 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4459, limit := 4459 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 4352, limit := 5720 } = .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 4459, limit := 5720 }) := by
  refine code_eq_of_parts (size := 106)
    (payload := { bytes := artifactBytes, pos := 4353, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4356, limit := 4459 })
    (bodyFinish := { bytes := artifactBytes, pos := 4459, limit := 4459 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_42_tail0
  · rfl

#print axioms code42_decoded

end Project.EulerOutwardGrid.Artifact
