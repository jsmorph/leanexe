import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_tail0 :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 2407, limit := 2530 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2530, limit := 2530 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 2403, limit := 5720 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 2530, limit := 5720 }) := by
  refine code_eq_of_parts (size := 126)
    (payload := { bytes := artifactBytes, pos := 2404, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2407, limit := 2530 })
    (bodyFinish := { bytes := artifactBytes, pos := 2530, limit := 2530 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_26_tail0
  · rfl

#print axioms code26_decoded

end Project.EulerOutwardGrid.Artifact
