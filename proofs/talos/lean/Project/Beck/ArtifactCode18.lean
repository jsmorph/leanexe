import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_18_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 6144, limit := 6151 } =
      .ok ((((Cache.raw.codes[18]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6151, limit := 6151 }) := by
  cbv

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 6140, limit := 27068 } = .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 6151, limit := 27068 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 6141, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 6144, limit := 6151 })
    (bodyFinish := { bytes := artifactBytes, pos := 6151, limit := 6151 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_18_tail0
  · rfl

#print axioms code18_decoded

end Project.Beck.Artifact
