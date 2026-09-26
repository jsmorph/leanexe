import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_22_tail0 :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 2130, limit := 2209 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2209, limit := 2209 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2126, limit := 5720 } = .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2209, limit := 5720 }) := by
  refine code_eq_of_parts (size := 82)
    (payload := { bytes := artifactBytes, pos := 2127, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2130, limit := 2209 })
    (bodyFinish := { bytes := artifactBytes, pos := 2209, limit := 2209 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_22_tail0
  · rfl

#print axioms code22_decoded

end Project.EulerOutwardGrid.Artifact
