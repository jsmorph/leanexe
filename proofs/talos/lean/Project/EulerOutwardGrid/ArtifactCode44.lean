import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_44_tail0 :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 4492, limit := 4565 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4565, limit := 4565 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 4488, limit := 5720 } = .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 4565, limit := 5720 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 4489, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4492, limit := 4565 })
    (bodyFinish := { bytes := artifactBytes, pos := 4565, limit := 4565 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_44_tail0
  · rfl

#print axioms code44_decoded

end Project.EulerOutwardGrid.Artifact
