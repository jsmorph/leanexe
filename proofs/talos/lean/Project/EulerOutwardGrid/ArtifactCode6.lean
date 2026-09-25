import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 797, limit := 830 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 830, limit := 830 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 793, limit := 5720 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 830, limit := 5720 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 794, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 797, limit := 830 })
    (bodyFinish := { bytes := artifactBytes, pos := 830, limit := 830 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.EulerOutwardGrid.Artifact
