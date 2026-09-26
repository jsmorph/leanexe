import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_27_tail0 :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 2535, limit := 2660 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2660, limit := 2660 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 2530, limit := 5720 } = .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 2660, limit := 5720 }) := by
  refine code_eq_of_parts (size := 128)
    (payload := { bytes := artifactBytes, pos := 2532, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2535, limit := 2660 })
    (bodyFinish := { bytes := artifactBytes, pos := 2660, limit := 2660 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_27_tail0
  · rfl

#print axioms code27_decoded

end Project.EulerOutwardGrid.Artifact
