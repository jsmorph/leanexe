import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_16_tail0 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 5627, limit := 5640 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5640, limit := 5640 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 5623, limit := 27068 } = .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 5640, limit := 27068 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 5624, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5627, limit := 5640 })
    (bodyFinish := { bytes := artifactBytes, pos := 5640, limit := 5640 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_16_tail0
  · rfl

#print axioms code16_decoded

end Project.Beck.Artifact
