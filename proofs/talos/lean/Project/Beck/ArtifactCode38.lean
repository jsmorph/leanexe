import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_38_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 26638, limit := 26715 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26715, limit := 26715 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 26634, limit := 27068 } = .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 26715, limit := 27068 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 26635, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 26638, limit := 26715 })
    (bodyFinish := { bytes := artifactBytes, pos := 26715, limit := 26715 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_38_tail0
  · rfl

#print axioms code38_decoded

end Project.Beck.Artifact
