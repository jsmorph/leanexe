import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2213, limit := 2278 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2278, limit := 2278 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2209, limit := 5720 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 2278, limit := 5720 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2210, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2213, limit := 2278 })
    (bodyFinish := { bytes := artifactBytes, pos := 2278, limit := 2278 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_23_tail0
  · rfl

#print axioms code23_decoded

end Project.EulerOutwardGrid.Artifact
