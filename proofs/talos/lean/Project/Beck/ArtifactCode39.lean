import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_39_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 26908, limit := 27068 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 43, .end), { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  cbv

@[cbv_eval] theorem sequence_39_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 26779, limit := 27068 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 25, .end), { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  cbv

@[cbv_eval] theorem sequence_39_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 26720, limit := 27068 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 26715, limit := 27068 } = .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 27068, limit := 27068 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 26717, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 26720, limit := 27068 })
    (bodyFinish := { bytes := artifactBytes, pos := 27068, limit := 27068 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_39_tail0
  · rfl

#print axioms code39_decoded

end Project.Beck.Artifact
