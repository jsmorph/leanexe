import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_18_tail0 :
    instructionSequenceAt 112 false { bytes := artifactBytes, pos := 1479, limit := 1591 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1591, limit := 1591 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 1475, limit := 5720 } = .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 1591, limit := 5720 }) := by
  refine code_eq_of_parts (size := 115)
    (payload := { bytes := artifactBytes, pos := 1476, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1479, limit := 1591 })
    (bodyFinish := { bytes := artifactBytes, pos := 1591, limit := 1591 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_18_tail0
  · rfl

#print axioms code18_decoded

end Project.EulerOutwardGrid.Artifact
