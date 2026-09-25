import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 1064, limit := 1082 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1082, limit := 1082 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1060, limit := 5720 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1082, limit := 5720 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 1061, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1064, limit := 1082 })
    (bodyFinish := { bytes := artifactBytes, pos := 1082, limit := 1082 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.EulerOutwardGrid.Artifact
