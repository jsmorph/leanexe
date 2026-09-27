import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_22_tail0 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 8194, limit := 8207 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8207, limit := 8207 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 8190, limit := 27068 } = .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 8207, limit := 27068 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 8191, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 8194, limit := 8207 })
    (bodyFinish := { bytes := artifactBytes, pos := 8207, limit := 8207 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_22_tail0
  · rfl

#print axioms code22_decoded

end Project.Beck.Artifact
