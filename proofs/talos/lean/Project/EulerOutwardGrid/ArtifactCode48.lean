import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_48_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 5290, limit := 5367 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5367, limit := 5367 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 5286, limit := 5720 } = .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 5367, limit := 5720 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 5287, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 5290, limit := 5367 })
    (bodyFinish := { bytes := artifactBytes, pos := 5367, limit := 5367 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_48_tail0
  · rfl

#print axioms code48_decoded

end Project.EulerOutwardGrid.Artifact
