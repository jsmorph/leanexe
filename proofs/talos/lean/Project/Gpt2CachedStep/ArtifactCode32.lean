import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_36_t_0_t_tail18 :
    instructionSequenceAt 471 false { bytes := artifactBytes, pos := 11996, limit := 12388 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 12124, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_36_t_0_t_tail0 :
    instructionSequenceAt 489 false { bytes := artifactBytes, pos := 11965, limit := 12388 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12124, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_36_t_tail0 :
    instructionSequenceAt 491 false { bytes := artifactBytes, pos := 11963, limit := 12388 } =
      .ok ((((((Cache.raw.codes[32]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12125, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_40_t_tail8 :
    instructionSequenceAt 479 true { bytes := artifactBytes, pos := 12145, limit := 12388 } =
      .ok ((((((Cache.raw.codes[32]!).body)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 12276, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_40_t_tail0 :
    instructionSequenceAt 487 true { bytes := artifactBytes, pos := 12132, limit := 12388 } =
      .ok ((((((Cache.raw.codes[32]!).body)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12276, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail40 :
    instructionSequenceAt 489 false { bytes := artifactBytes, pos := 12130, limit := 12388 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 40, .end), { bytes := artifactBytes, pos := 12388, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail36 :
    instructionSequenceAt 493 false { bytes := artifactBytes, pos := 11961, limit := 12388 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 36, .end), { bytes := artifactBytes, pos := 12388, limit := 12388 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail0 :
    instructionSequenceAt 529 false { bytes := artifactBytes, pos := 11859, limit := 12388 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12388, limit := 12388 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 11854, limit := 19083 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 12388, limit := 19083 }) := by
  refine code_eq_of_parts (size := 532)
    (payload := { bytes := artifactBytes, pos := 11856, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 11859, limit := 12388 })
    (bodyFinish := { bytes := artifactBytes, pos := 12388, limit := 12388 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_32_tail0
  · rfl

#print axioms code32_decoded

end Project.Gpt2CachedStep.Artifact
