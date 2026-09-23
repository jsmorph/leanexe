import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4005, limit := 4295 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4133, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 3974, limit := 4295 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4133, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 3972, limit := 4295 } =
      .ok ((((((Cache.raw.codes[9]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4134, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 4154, limit := 4295 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4285, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 4141, limit := 4295 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4285, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4139, limit := 4295 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4295, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 3970, limit := 4295 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 18, .end), { bytes := artifactBytes, pos := 4295, limit := 4295 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 3933, limit := 4295 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4295, limit := 4295 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 3928, limit := 4757 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 4295, limit := 4757 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 3930, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 3933, limit := 4295 })
    (bodyFinish := { bytes := artifactBytes, pos := 4295, limit := 4295 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
