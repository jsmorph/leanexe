import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_16_tail0 :
    instructionSequenceAt 55 false { bytes := artifactBytes, pos := 1345, limit := 1400 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1400, limit := 1400 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1341, limit := 5720 } = .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1400, limit := 5720 }) := by
  refine code_eq_of_parts (size := 58)
    (payload := { bytes := artifactBytes, pos := 1342, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1345, limit := 1400 })
    (bodyFinish := { bytes := artifactBytes, pos := 1400, limit := 1400 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_16_tail0
  · rfl

#print axioms code16_decoded

end Project.EulerOutwardGrid.Artifact
