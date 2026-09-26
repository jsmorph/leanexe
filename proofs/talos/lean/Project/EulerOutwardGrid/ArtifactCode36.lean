import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_36_tail0 :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3927, limit := 4042 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4042, limit := 4042 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 3923, limit := 5720 } = .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4042, limit := 5720 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3924, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3927, limit := 4042 })
    (bodyFinish := { bytes := artifactBytes, pos := 4042, limit := 4042 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_36_tail0
  · rfl

#print axioms code36_decoded

end Project.EulerOutwardGrid.Artifact
