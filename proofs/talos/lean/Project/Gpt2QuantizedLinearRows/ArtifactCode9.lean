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
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 3989, limit := 4279 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4117, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 3958, limit := 4279 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4117, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 3956, limit := 4279 } =
      .ok ((((((Cache.raw.codes[9]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4118, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 4138, limit := 4279 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4269, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 4125, limit := 4279 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4269, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4123, limit := 4279 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4279, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 3954, limit := 4279 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 18, .end), { bytes := artifactBytes, pos := 4279, limit := 4279 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 3917, limit := 4279 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4279, limit := 4279 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 3912, limit := 4741 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 4279, limit := 4741 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 3914, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 3917, limit := 4279 })
    (bodyFinish := { bytes := artifactBytes, pos := 4279, limit := 4279 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
