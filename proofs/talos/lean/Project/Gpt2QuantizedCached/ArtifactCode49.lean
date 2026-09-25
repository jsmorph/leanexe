import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_49_10_t_0_t_tail19 :
    instructionSequenceAt 170 false { bytes := artifactBytes, pos := 15519, limit := 15663 } =
      .ok ((((((((Cache.raw.codes[49]!).body)[10]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 15647, limit := 15663 }) := by
  cbv

@[cbv_eval] theorem sequence_49_10_t_0_t_tail0 :
    instructionSequenceAt 189 false { bytes := artifactBytes, pos := 15484, limit := 15663 } =
      .ok ((((((((Cache.raw.codes[49]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15647, limit := 15663 }) := by
  cbv

@[cbv_eval] theorem sequence_49_10_t_tail0 :
    instructionSequenceAt 191 false { bytes := artifactBytes, pos := 15482, limit := 15663 } =
      .ok ((((((Cache.raw.codes[49]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15648, limit := 15663 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail10 :
    instructionSequenceAt 193 false { bytes := artifactBytes, pos := 15480, limit := 15663 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 10, .end), { bytes := artifactBytes, pos := 15663, limit := 15663 }) := by
  cbv

@[cbv_eval] theorem sequence_49_tail0 :
    instructionSequenceAt 203 false { bytes := artifactBytes, pos := 15460, limit := 15663 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15663, limit := 15663 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 15455, limit := 28017 } = .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 15663, limit := 28017 }) := by
  refine code_eq_of_parts (size := 206)
    (payload := { bytes := artifactBytes, pos := 15457, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 15460, limit := 15663 })
    (bodyFinish := { bytes := artifactBytes, pos := 15663, limit := 15663 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_49_tail0
  · rfl

#print axioms code49_decoded

end Project.Gpt2QuantizedCached.Artifact
