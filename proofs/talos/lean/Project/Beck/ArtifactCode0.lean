import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_32_t_0_t_tail18 :
    instructionSequenceAt 363 false { bytes := artifactBytes, pos := 726, limit := 1046 } =
      .ok ((((((((Cache.raw.codes[0]!).body)[32]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 854, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_32_t_0_t_tail0 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 695, limit := 1046 } =
      .ok ((((((((Cache.raw.codes[0]!).body)[32]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 854, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_32_t_tail0 :
    instructionSequenceAt 383 false { bytes := artifactBytes, pos := 693, limit := 1046 } =
      .ok ((((((Cache.raw.codes[0]!).body)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 855, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_36_t_tail8 :
    instructionSequenceAt 371 true { bytes := artifactBytes, pos := 875, limit := 1046 } =
      .ok ((((((Cache.raw.codes[0]!).body)[36]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1006, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_36_t_tail0 :
    instructionSequenceAt 379 true { bytes := artifactBytes, pos := 862, limit := 1046 } =
      .ok ((((((Cache.raw.codes[0]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1006, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail36 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 860, limit := 1046 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 36, .end), { bytes := artifactBytes, pos := 1046, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail32 :
    instructionSequenceAt 385 false { bytes := artifactBytes, pos := 691, limit := 1046 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 32, .end), { bytes := artifactBytes, pos := 1046, limit := 1046 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 417 false { bytes := artifactBytes, pos := 629, limit := 1046 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1046, limit := 1046 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 624, limit := 27068 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 1046, limit := 27068 }) := by
  refine code_eq_of_parts (size := 420)
    (payload := { bytes := artifactBytes, pos := 626, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 629, limit := 1046 })
    (bodyFinish := { bytes := artifactBytes, pos := 1046, limit := 1046 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.Beck.Artifact
