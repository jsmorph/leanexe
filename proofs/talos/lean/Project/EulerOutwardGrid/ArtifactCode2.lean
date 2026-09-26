import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 606, limit := 619 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 619, limit := 619 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 602, limit := 5720 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 619, limit := 5720 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 603, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 606, limit := 619 })
    (bodyFinish := { bytes := artifactBytes, pos := 619, limit := 619 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.EulerOutwardGrid.Artifact
