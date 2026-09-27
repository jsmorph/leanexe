import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 27 false { bytes := artifactBytes, pos := 5038, limit := 5065 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5065, limit := 5065 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 5034, limit := 27068 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 5065, limit := 27068 }) := by
  refine code_eq_of_parts (size := 30)
    (payload := { bytes := artifactBytes, pos := 5035, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5038, limit := 5065 })
    (bodyFinish := { bytes := artifactBytes, pos := 5065, limit := 5065 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Beck.Artifact
