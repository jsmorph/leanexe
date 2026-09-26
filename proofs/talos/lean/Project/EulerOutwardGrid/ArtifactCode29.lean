import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_29_tail0 :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2776, limit := 2884 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2884, limit := 2884 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 2772, limit := 5720 } = .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 2884, limit := 5720 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2773, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2776, limit := 2884 })
    (bodyFinish := { bytes := artifactBytes, pos := 2884, limit := 2884 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_29_tail0
  · rfl

#print axioms code29_decoded

end Project.EulerOutwardGrid.Artifact
