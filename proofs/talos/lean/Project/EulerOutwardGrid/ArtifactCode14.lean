import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_14_tail0 :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 1231, limit := 1309 } =
      .ok ((((Cache.raw.codes[14]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1309, limit := 1309 }) := by
  cbv

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 1227, limit := 5720 } = .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 1309, limit := 5720 }) := by
  refine code_eq_of_parts (size := 81)
    (payload := { bytes := artifactBytes, pos := 1228, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1231, limit := 1309 })
    (bodyFinish := { bytes := artifactBytes, pos := 1309, limit := 1309 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_14_tail0
  · rfl

#print axioms code14_decoded

end Project.EulerOutwardGrid.Artifact
