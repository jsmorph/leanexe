import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_12_t_0_t_tail21 :
    instructionSequenceAt 189 false { bytes := artifactBytes, pos := 6694, limit := 6851 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 6822, limit := 6851 }) := by
  cbv

@[cbv_eval] theorem sequence_32_12_t_0_t_tail0 :
    instructionSequenceAt 210 false { bytes := artifactBytes, pos := 6654, limit := 6851 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6822, limit := 6851 }) := by
  cbv

@[cbv_eval] theorem sequence_32_12_t_tail0 :
    instructionSequenceAt 212 false { bytes := artifactBytes, pos := 6652, limit := 6851 } =
      .ok ((((((Cache.raw.codes[32]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6823, limit := 6851 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail12 :
    instructionSequenceAt 214 false { bytes := artifactBytes, pos := 6650, limit := 6851 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 12, .end), { bytes := artifactBytes, pos := 6851, limit := 6851 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail0 :
    instructionSequenceAt 226 false { bytes := artifactBytes, pos := 6625, limit := 6851 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6851, limit := 6851 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 6620, limit := 28315 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 6851, limit := 28315 }) := by
  refine code_eq_of_parts (size := 229)
    (payload := { bytes := artifactBytes, pos := 6622, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 6625, limit := 6851 })
    (bodyFinish := { bytes := artifactBytes, pos := 6851, limit := 6851 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_32_tail0
  · rfl

#print axioms code32_decoded

end Project.Gpt2QuantizedCached.Artifact
