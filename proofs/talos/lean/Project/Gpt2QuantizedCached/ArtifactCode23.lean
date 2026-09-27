import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_10_t_0_t_tail12 :
    instructionSequenceAt 176 false { bytes := artifactBytes, pos := 2858, limit := 3015 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[10]!).childBody false)[0]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 2999, limit := 3015 }) := by
  cbv

@[cbv_eval] theorem sequence_23_10_t_0_t_tail0 :
    instructionSequenceAt 188 false { bytes := artifactBytes, pos := 2837, limit := 3015 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2999, limit := 3015 }) := by
  cbv

@[cbv_eval] theorem sequence_23_10_t_tail0 :
    instructionSequenceAt 190 false { bytes := artifactBytes, pos := 2835, limit := 3015 } =
      .ok ((((((Cache.raw.codes[23]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3000, limit := 3015 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail10 :
    instructionSequenceAt 192 false { bytes := artifactBytes, pos := 2833, limit := 3015 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 10, .end), { bytes := artifactBytes, pos := 3015, limit := 3015 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail0 :
    instructionSequenceAt 202 false { bytes := artifactBytes, pos := 2813, limit := 3015 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3015, limit := 3015 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2808, limit := 28017 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3015, limit := 28017 }) := by
  refine code_eq_of_parts (size := 205)
    (payload := { bytes := artifactBytes, pos := 2810, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 2813, limit := 3015 })
    (bodyFinish := { bytes := artifactBytes, pos := 3015, limit := 3015 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_23_tail0
  · rfl

#print axioms code23_decoded

end Project.Gpt2QuantizedCached.Artifact
