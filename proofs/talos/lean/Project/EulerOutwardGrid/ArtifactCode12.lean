import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 42 false { bytes := artifactBytes, pos := 1086, limit := 1128 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1128, limit := 1128 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 1082, limit := 5720 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 1128, limit := 5720 }) := by
  refine code_eq_of_parts (size := 45)
    (payload := { bytes := artifactBytes, pos := 1083, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1086, limit := 1128 })
    (bodyFinish := { bytes := artifactBytes, pos := 1128, limit := 1128 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.EulerOutwardGrid.Artifact
