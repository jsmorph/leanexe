import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_48_3_e_16_t_0_t_tail13 :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 15278, limit := 15575 } =
      .ok ((((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[16]!).childBody false)[0]!).childBody false).drop 13, .end), { bytes := artifactBytes, pos := 15418, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_16_t_0_t_tail0 :
    instructionSequenceAt 352 false { bytes := artifactBytes, pos := 15250, limit := 15575 } =
      .ok ((((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[16]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15418, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_16_t_tail0 :
    instructionSequenceAt 354 false { bytes := artifactBytes, pos := 15248, limit := 15575 } =
      .ok ((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[16]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15419, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail29 :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 15443, limit := 15575 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 29, .end), { bytes := artifactBytes, pos := 15572, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail16 :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 15246, limit := 15575 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 16, .end), { bytes := artifactBytes, pos := 15572, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail0 :
    instructionSequenceAt 372 false { bytes := artifactBytes, pos := 15214, limit := 15575 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 15572, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_tail3 :
    instructionSequenceAt 374 false { bytes := artifactBytes, pos := 15207, limit := 15575 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 3, .end), { bytes := artifactBytes, pos := 15575, limit := 15575 }) := by
  cbv

@[cbv_eval] theorem sequence_48_tail0 :
    instructionSequenceAt 377 false { bytes := artifactBytes, pos := 15198, limit := 15575 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15575, limit := 15575 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 15193, limit := 28315 } = .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 15575, limit := 28315 }) := by
  refine code_eq_of_parts (size := 380)
    (payload := { bytes := artifactBytes, pos := 15195, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 15198, limit := 15575 })
    (bodyFinish := { bytes := artifactBytes, pos := 15575, limit := 15575 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_48_tail0
  · rfl

#print axioms code48_decoded

end Project.Gpt2QuantizedCached.Artifact
