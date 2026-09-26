import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1027, limit := 1060 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1060, limit := 1060 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1023, limit := 5720 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1060, limit := 5720 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 1024, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1027, limit := 1060 })
    (bodyFinish := { bytes := artifactBytes, pos := 1060, limit := 1060 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.EulerOutwardGrid.Artifact
