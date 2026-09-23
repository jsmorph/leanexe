import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_38_12_t_0_t_tail38 :
    instructionSequenceAt 206 false { bytes := artifactBytes, pos := 11011, limit := 11156 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[12]!).childBody false)[0]!).childBody false).drop 38, .end), { bytes := artifactBytes, pos := 11140, limit := 11156 }) := by
  cbv

@[cbv_eval] theorem sequence_38_12_t_0_t_tail0 :
    instructionSequenceAt 244 false { bytes := artifactBytes, pos := 10924, limit := 11156 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11140, limit := 11156 }) := by
  cbv

@[cbv_eval] theorem sequence_38_12_t_tail0 :
    instructionSequenceAt 246 false { bytes := artifactBytes, pos := 10922, limit := 11156 } =
      .ok ((((((Cache.raw.codes[38]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11141, limit := 11156 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail12 :
    instructionSequenceAt 248 false { bytes := artifactBytes, pos := 10920, limit := 11156 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 12, .end), { bytes := artifactBytes, pos := 11156, limit := 11156 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail0 :
    instructionSequenceAt 260 false { bytes := artifactBytes, pos := 10896, limit := 11156 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11156, limit := 11156 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 10891, limit := 28315 } = .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 11156, limit := 28315 }) := by
  refine code_eq_of_parts (size := 263)
    (payload := { bytes := artifactBytes, pos := 10893, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 10896, limit := 11156 })
    (bodyFinish := { bytes := artifactBytes, pos := 11156, limit := 11156 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_38_tail0
  · rfl

#print axioms code38_decoded

end Project.Gpt2QuantizedCached.Artifact
