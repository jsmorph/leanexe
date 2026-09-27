import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 5069, limit := 5112 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5112, limit := 5112 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 5065, limit := 27068 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 5112, limit := 27068 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 5066, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5069, limit := 5112 })
    (bodyFinish := { bytes := artifactBytes, pos := 5112, limit := 5112 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.Beck.Artifact
