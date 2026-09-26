import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_10_t_0_t_tail12 :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 3368, limit := 3566 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[10]!).childBody false)[0]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 3550, limit := 3566 }) := by
  cbv

@[cbv_eval] theorem sequence_26_10_t_0_t_tail0 :
    instructionSequenceAt 229 false { bytes := artifactBytes, pos := 3347, limit := 3566 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3550, limit := 3566 }) := by
  cbv

@[cbv_eval] theorem sequence_26_10_t_tail0 :
    instructionSequenceAt 231 false { bytes := artifactBytes, pos := 3345, limit := 3566 } =
      .ok ((((((Cache.raw.codes[26]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3551, limit := 3566 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail10 :
    instructionSequenceAt 233 false { bytes := artifactBytes, pos := 3343, limit := 3566 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 10, .end), { bytes := artifactBytes, pos := 3566, limit := 3566 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail0 :
    instructionSequenceAt 243 false { bytes := artifactBytes, pos := 3323, limit := 3566 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3566, limit := 3566 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 3318, limit := 28017 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3566, limit := 28017 }) := by
  refine code_eq_of_parts (size := 246)
    (payload := { bytes := artifactBytes, pos := 3320, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 3323, limit := 3566 })
    (bodyFinish := { bytes := artifactBytes, pos := 3566, limit := 3566 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_26_tail0
  · rfl

#print axioms code26_decoded

end Project.Gpt2QuantizedCached.Artifact
