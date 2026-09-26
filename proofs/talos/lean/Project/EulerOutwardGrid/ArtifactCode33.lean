import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_tail0 :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3471, limit := 3600 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3600, limit := 3600 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3466, limit := 5720 } = .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3600, limit := 5720 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3468, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3471, limit := 3600 })
    (bodyFinish := { bytes := artifactBytes, pos := 3600, limit := 3600 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_33_tail0
  · rfl

#print axioms code33_decoded

end Project.EulerOutwardGrid.Artifact
