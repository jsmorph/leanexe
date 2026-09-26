import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2282, limit := 2347 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2347, limit := 2347 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 2278, limit := 5720 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 2347, limit := 5720 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2279, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2282, limit := 2347 })
    (bodyFinish := { bytes := artifactBytes, pos := 2347, limit := 2347 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_24_tail0
  · rfl

#print axioms code24_decoded

end Project.EulerOutwardGrid.Artifact
