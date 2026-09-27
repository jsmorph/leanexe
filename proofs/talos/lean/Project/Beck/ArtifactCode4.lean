import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2040, limit := 2053 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2053, limit := 2053 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 2036, limit := 27068 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 2053, limit := 27068 }) := by
  refine code_eq_of_parts (size := 16)
    (payload := { bytes := artifactBytes, pos := 2037, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 2040, limit := 2053 })
    (bodyFinish := { bytes := artifactBytes, pos := 2053, limit := 2053 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Beck.Artifact
