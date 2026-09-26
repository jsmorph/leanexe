import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 584, limit := 591 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 591, limit := 591 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 580, limit := 5720 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 591, limit := 5720 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 581, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 584, limit := 591 })
    (bodyFinish := { bytes := artifactBytes, pos := 591, limit := 591 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.EulerOutwardGrid.Artifact
