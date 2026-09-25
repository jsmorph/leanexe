import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_tail0 :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 3816, limit := 3923 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3923, limit := 3923 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3812, limit := 5720 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 3923, limit := 5720 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 3813, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3816, limit := 3923 })
    (bodyFinish := { bytes := artifactBytes, pos := 3923, limit := 3923 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_35_tail0
  · rfl

#print axioms code35_decoded

end Project.EulerOutwardGrid.Artifact
