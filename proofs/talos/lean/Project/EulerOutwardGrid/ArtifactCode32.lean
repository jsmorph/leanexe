import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_tail0 :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3351, limit := 3466 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3466, limit := 3466 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3347, limit := 5720 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3466, limit := 5720 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3348, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3351, limit := 3466 })
    (bodyFinish := { bytes := artifactBytes, pos := 3466, limit := 3466 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_32_tail0
  · rfl

#print axioms code32_decoded

end Project.EulerOutwardGrid.Artifact
