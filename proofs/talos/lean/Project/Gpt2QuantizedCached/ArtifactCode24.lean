import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_10_t_0_t_tail34 :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 3134, limit := 3278 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[10]!).childBody false)[0]!).childBody false).drop 34, .end), { bytes := artifactBytes, pos := 3262, limit := 3278 }) := by
  cbv

@[cbv_eval] theorem sequence_24_10_t_0_t_tail0 :
    instructionSequenceAt 244 false { bytes := artifactBytes, pos := 3044, limit := 3278 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3262, limit := 3278 }) := by
  cbv

@[cbv_eval] theorem sequence_24_10_t_tail0 :
    instructionSequenceAt 246 false { bytes := artifactBytes, pos := 3042, limit := 3278 } =
      .ok ((((((Cache.raw.codes[24]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3263, limit := 3278 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail10 :
    instructionSequenceAt 248 false { bytes := artifactBytes, pos := 3040, limit := 3278 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 10, .end), { bytes := artifactBytes, pos := 3278, limit := 3278 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail0 :
    instructionSequenceAt 258 false { bytes := artifactBytes, pos := 3020, limit := 3278 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3278, limit := 3278 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 3015, limit := 28017 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3278, limit := 28017 }) := by
  refine code_eq_of_parts (size := 261)
    (payload := { bytes := artifactBytes, pos := 3017, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 3020, limit := 3278 })
    (bodyFinish := { bytes := artifactBytes, pos := 3278, limit := 3278 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_24_tail0
  · rfl

#print axioms code24_decoded

end Project.Gpt2QuantizedCached.Artifact
