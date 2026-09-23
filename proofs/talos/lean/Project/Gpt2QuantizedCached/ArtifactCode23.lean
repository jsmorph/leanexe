import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_12_t_0_t_tail12 :
    instructionSequenceAt 182 false { bytes := artifactBytes, pos := 2862, limit := 3023 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[12]!).childBody false)[0]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 3007, limit := 3023 }) := by
  cbv

@[cbv_eval] theorem sequence_23_12_t_0_t_tail0 :
    instructionSequenceAt 194 false { bytes := artifactBytes, pos := 2841, limit := 3023 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3007, limit := 3023 }) := by
  cbv

@[cbv_eval] theorem sequence_23_12_t_tail0 :
    instructionSequenceAt 196 false { bytes := artifactBytes, pos := 2839, limit := 3023 } =
      .ok ((((((Cache.raw.codes[23]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3008, limit := 3023 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail12 :
    instructionSequenceAt 198 false { bytes := artifactBytes, pos := 2837, limit := 3023 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 12, .end), { bytes := artifactBytes, pos := 3023, limit := 3023 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail0 :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 2813, limit := 3023 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3023, limit := 3023 }) := by
  cbv

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 2808, limit := 28315 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3023, limit := 28315 }) := by
  refine code_eq_of_parts (size := 213)
    (payload := { bytes := artifactBytes, pos := 2810, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 2813, limit := 3023 })
    (bodyFinish := { bytes := artifactBytes, pos := 3023, limit := 3023 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_23_tail0
  · rfl

#print axioms code23_decoded

end Project.Gpt2QuantizedCached.Artifact
