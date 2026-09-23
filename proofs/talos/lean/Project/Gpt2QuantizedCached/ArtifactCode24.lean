import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_12_t_0_t_tail34 :
    instructionSequenceAt 216 false { bytes := artifactBytes, pos := 3146, limit := 3294 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[12]!).childBody false)[0]!).childBody false).drop 34, .end), { bytes := artifactBytes, pos := 3278, limit := 3294 }) := by
  cbv

@[cbv_eval] theorem sequence_24_12_t_0_t_tail0 :
    instructionSequenceAt 250 false { bytes := artifactBytes, pos := 3056, limit := 3294 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3278, limit := 3294 }) := by
  cbv

@[cbv_eval] theorem sequence_24_12_t_tail0 :
    instructionSequenceAt 252 false { bytes := artifactBytes, pos := 3054, limit := 3294 } =
      .ok ((((((Cache.raw.codes[24]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3279, limit := 3294 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail12 :
    instructionSequenceAt 254 false { bytes := artifactBytes, pos := 3052, limit := 3294 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 12, .end), { bytes := artifactBytes, pos := 3294, limit := 3294 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail0 :
    instructionSequenceAt 266 false { bytes := artifactBytes, pos := 3028, limit := 3294 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3294, limit := 3294 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 3023, limit := 28315 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3294, limit := 28315 }) := by
  refine code_eq_of_parts (size := 269)
    (payload := { bytes := artifactBytes, pos := 3025, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 3028, limit := 3294 })
    (bodyFinish := { bytes := artifactBytes, pos := 3294, limit := 3294 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_24_tail0
  · rfl

#print axioms code24_decoded

end Project.Gpt2QuantizedCached.Artifact
