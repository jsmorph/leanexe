import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_tail0 :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 1595, limit := 1659 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1659, limit := 1659 }) := by
  cbv

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 1591, limit := 5720 } = .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 1659, limit := 5720 }) := by
  refine code_eq_of_parts (size := 67)
    (payload := { bytes := artifactBytes, pos := 1592, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1595, limit := 1659 })
    (bodyFinish := { bytes := artifactBytes, pos := 1659, limit := 1659 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_19_tail0
  · rfl

#print axioms code19_decoded

end Project.EulerOutwardGrid.Artifact
