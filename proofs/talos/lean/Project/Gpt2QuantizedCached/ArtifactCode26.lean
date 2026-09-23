import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_26_12_t_0_t_tail12 :
    instructionSequenceAt 223 false { bytes := artifactBytes, pos := 3388, limit := 3590 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[12]!).childBody false)[0]!).childBody false).drop 12, .end), { bytes := artifactBytes, pos := 3574, limit := 3590 }) := by
  cbv

@[cbv_eval] theorem sequence_26_12_t_0_t_tail0 :
    instructionSequenceAt 235 false { bytes := artifactBytes, pos := 3367, limit := 3590 } =
      .ok ((((((((Cache.raw.codes[26]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3574, limit := 3590 }) := by
  cbv

@[cbv_eval] theorem sequence_26_12_t_tail0 :
    instructionSequenceAt 237 false { bytes := artifactBytes, pos := 3365, limit := 3590 } =
      .ok ((((((Cache.raw.codes[26]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3575, limit := 3590 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail12 :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 3363, limit := 3590 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 12, .end), { bytes := artifactBytes, pos := 3590, limit := 3590 }) := by
  cbv

@[cbv_eval] theorem sequence_26_tail0 :
    instructionSequenceAt 251 false { bytes := artifactBytes, pos := 3339, limit := 3590 } =
      .ok ((((Cache.raw.codes[26]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3590, limit := 3590 }) := by
  cbv

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 3334, limit := 28315 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3590, limit := 28315 }) := by
  refine code_eq_of_parts (size := 254)
    (payload := { bytes := artifactBytes, pos := 3336, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 3339, limit := 3590 })
    (bodyFinish := { bytes := artifactBytes, pos := 3590, limit := 3590 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_26_tail0
  · rfl

#print axioms code26_decoded

end Project.Gpt2QuantizedCached.Artifact
