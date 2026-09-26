import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_tail29 :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3671, limit := 3812 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 29, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail0 :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3605, limit := 3812 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3600, limit := 5720 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3812, limit := 5720 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3602, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 3605, limit := 3812 })
    (bodyFinish := { bytes := artifactBytes, pos := 3812, limit := 3812 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_34_tail0
  · rfl

#print axioms code34_decoded

end Project.EulerOutwardGrid.Artifact
