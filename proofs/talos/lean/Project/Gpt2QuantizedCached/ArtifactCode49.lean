import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_49_12_t_0_t_tail21 :
    instructionSequenceAt 174 false { bytes := artifactBytes, pos := 15647, limit := 15791 } =
      .ok ((((((((Cache.raw.codes[49]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 15775, limit := 15791 }) := by
  cbv

@[cbv_eval] theorem sequence_49_12_t_0_t_tail0 :
    instructionSequenceAt 195 false { bytes := artifactBytes, pos := 15608, limit := 15791 } =
      .ok ((((((((Cache.raw.codes[49]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15775, limit := 15791 }) := by
  cbv

@[cbv_eval] theorem sequence_49_12_t_tail0 :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 15606, limit := 15791 } =
      .ok ((((((Cache.raw.codes[49]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15776, limit := 15791 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail12 :
    instructionSequenceAt 199 false { bytes := artifactBytes, pos := 15604, limit := 15791 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 12, .end), { bytes := artifactBytes, pos := 15791, limit := 15791 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail0 :
    instructionSequenceAt 211 false { bytes := artifactBytes, pos := 15580, limit := 15791 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15791, limit := 15791 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 15575, limit := 28315 } = .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 15791, limit := 28315 }) := by
  refine code_eq_of_parts (size := 214)
    (payload := { bytes := artifactBytes, pos := 15577, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 15580, limit := 15791 })
    (bodyFinish := { bytes := artifactBytes, pos := 15791, limit := 15791 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_49_tail0
  · rfl

#print axioms code49_decoded

end Project.Gpt2QuantizedCached.Artifact
