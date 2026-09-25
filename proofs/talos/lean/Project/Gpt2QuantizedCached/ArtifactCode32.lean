import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_10_t_0_t_tail19 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 6653, limit := 6811 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[10]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 6782, limit := 6811 }) := by
  cbv

@[cbv_eval] theorem sequence_32_10_t_0_t_tail0 :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 6618, limit := 6811 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6782, limit := 6811 }) := by
  cbv

@[cbv_eval] theorem sequence_32_10_t_tail0 :
    instructionSequenceAt 206 false { bytes := artifactBytes, pos := 6616, limit := 6811 } =
      .ok ((((((Cache.raw.codes[32]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6783, limit := 6811 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail10 :
    instructionSequenceAt 208 false { bytes := artifactBytes, pos := 6614, limit := 6811 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 10, .end), { bytes := artifactBytes, pos := 6811, limit := 6811 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail0 :
    instructionSequenceAt 218 false { bytes := artifactBytes, pos := 6593, limit := 6811 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6811, limit := 6811 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 6588, limit := 28017 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 6811, limit := 28017 }) := by
  refine code_eq_of_parts (size := 221)
    (payload := { bytes := artifactBytes, pos := 6590, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 6593, limit := 6811 })
    (bodyFinish := { bytes := artifactBytes, pos := 6811, limit := 6811 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_32_tail0
  · rfl

#print axioms code32_decoded

end Project.Gpt2QuantizedCached.Artifact
