import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 774, limit := 793 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 793, limit := 793 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 770, limit := 5720 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 793, limit := 5720 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 771, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 774, limit := 793 })
    (bodyFinish := { bytes := artifactBytes, pos := 793, limit := 793 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.EulerOutwardGrid.Artifact
