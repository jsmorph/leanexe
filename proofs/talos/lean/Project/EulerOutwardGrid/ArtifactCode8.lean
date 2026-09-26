import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 962, limit := 1000 } =
      .ok ((((Cache.raw.codes[8]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1000, limit := 1000 }) := by
  cbv

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 958, limit := 5720 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 1000, limit := 5720 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 959, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 962, limit := 1000 })
    (bodyFinish := { bytes := artifactBytes, pos := 1000, limit := 1000 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.EulerOutwardGrid.Artifact
