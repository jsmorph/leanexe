import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 834, limit := 958 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 958, limit := 958 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 830, limit := 5720 } = .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 958, limit := 5720 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 831, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 834, limit := 958 })
    (bodyFinish := { bytes := artifactBytes, pos := 958, limit := 958 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.EulerOutwardGrid.Artifact
