import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 10506, limit := 10666 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 43, .end), { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 10377, limit := 10666 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 25, .end), { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 10318, limit := 10666 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 10313, limit := 10666 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 10666, limit := 10666 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 10315, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 10318, limit := 10666 })
    (bodyFinish := { bytes := artifactBytes, pos := 10666, limit := 10666 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.ExpArm.Artifact
