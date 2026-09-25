import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_tail0 :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 2351, limit := 2403 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2403, limit := 2403 }) := by
  cbv

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 2347, limit := 5720 } = .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 2403, limit := 5720 }) := by
  refine code_eq_of_parts (size := 55)
    (payload := { bytes := artifactBytes, pos := 2348, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2351, limit := 2403 })
    (bodyFinish := { bytes := artifactBytes, pos := 2403, limit := 2403 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_25_tail0
  · rfl

#print axioms code25_decoded

end Project.EulerOutwardGrid.Artifact
