import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_47_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 5260, limit := 5286 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5286, limit := 5286 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 5258, limit := 5720 } = .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 5286, limit := 5720 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 5259, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 5260, limit := 5286 })
    (bodyFinish := { bytes := artifactBytes, pos := 5286, limit := 5286 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_47_tail0
  · rfl

#print axioms code47_decoded

end Project.EulerOutwardGrid.Artifact
