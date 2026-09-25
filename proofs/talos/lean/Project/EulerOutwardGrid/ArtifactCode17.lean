import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_17_tail0 :
    instructionSequenceAt 71 false { bytes := artifactBytes, pos := 1404, limit := 1475 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1475, limit := 1475 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1400, limit := 5720 } = .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 1475, limit := 5720 }) := by
  refine code_eq_of_parts (size := 74)
    (payload := { bytes := artifactBytes, pos := 1401, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1404, limit := 1475 })
    (bodyFinish := { bytes := artifactBytes, pos := 1475, limit := 1475 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_17_tail0
  · rfl

#print axioms code17_decoded

end Project.EulerOutwardGrid.Artifact
