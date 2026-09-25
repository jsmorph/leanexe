import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_43_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 4463, limit := 4488 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4488, limit := 4488 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 4459, limit := 5720 } = .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 4488, limit := 5720 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 4460, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4463, limit := 4488 })
    (bodyFinish := { bytes := artifactBytes, pos := 4488, limit := 4488 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_43_tail0
  · rfl

#print axioms code43_decoded

end Project.EulerOutwardGrid.Artifact
