import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 5127, limit := 5193 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5193, limit := 5193 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 5123, limit := 27068 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 5193, limit := 27068 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 5124, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5127, limit := 5193 })
    (bodyFinish := { bytes := artifactBytes, pos := 5193, limit := 5193 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.Beck.Artifact
