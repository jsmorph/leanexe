import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_20_tail1 :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 1666, limit := 1795 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 1, .end), { bytes := artifactBytes, pos := 1795, limit := 1795 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail0 :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 1664, limit := 1795 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1795, limit := 1795 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 1659, limit := 5720 } = .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 1795, limit := 5720 }) := by
  refine code_eq_of_parts (size := 134)
    (payload := { bytes := artifactBytes, pos := 1661, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1664, limit := 1795 })
    (bodyFinish := { bytes := artifactBytes, pos := 1795, limit := 1795 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_20_tail0
  · rfl

#print axioms code20_decoded

end Project.EulerOutwardGrid.Artifact
