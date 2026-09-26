import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 623, limit := 728 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 728, limit := 728 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 619, limit := 5720 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 728, limit := 5720 }) := by
  refine code_eq_of_parts (size := 108)
    (payload := { bytes := artifactBytes, pos := 620, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 623, limit := 728 })
    (bodyFinish := { bytes := artifactBytes, pos := 728, limit := 728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.EulerOutwardGrid.Artifact
