import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_29_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 14007, limit := 14014 } =
      .ok ((((Cache.raw.codes[29]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14014, limit := 14014 }) := by
  cbv

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 14003, limit := 27068 } = .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 14014, limit := 27068 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 14004, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 14007, limit := 14014 })
    (bodyFinish := { bytes := artifactBytes, pos := 14014, limit := 14014 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_29_tail0
  · rfl

#print axioms code29_decoded

end Project.Beck.Artifact
