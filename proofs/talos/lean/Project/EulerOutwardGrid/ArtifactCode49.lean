import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_49_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 5560, limit := 5720 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 43, .end), { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 5431, limit := 5720 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 25, .end), { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 5372, limit := 5720 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 5367, limit := 5720 } = .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 5720, limit := 5720 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 5369, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 5372, limit := 5720 })
    (bodyFinish := { bytes := artifactBytes, pos := 5720, limit := 5720 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_49_tail0
  · rfl

#print axioms code49_decoded

end Project.EulerOutwardGrid.Artifact
