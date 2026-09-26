import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_41_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4345, limit := 4352 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4352, limit := 4352 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 4341, limit := 5720 } = .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 4352, limit := 5720 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4342, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4345, limit := 4352 })
    (bodyFinish := { bytes := artifactBytes, pos := 4352, limit := 4352 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_41_tail0
  · rfl

#print axioms code41_decoded

end Project.EulerOutwardGrid.Artifact
