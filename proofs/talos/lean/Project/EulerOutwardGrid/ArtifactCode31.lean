import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_31_tail0 :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 3239, limit := 3347 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3347, limit := 3347 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 3235, limit := 5720 } = .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 3347, limit := 5720 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 3236, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3239, limit := 3347 })
    (bodyFinish := { bytes := artifactBytes, pos := 3347, limit := 3347 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_31_tail0
  · rfl

#print axioms code31_decoded

end Project.EulerOutwardGrid.Artifact
