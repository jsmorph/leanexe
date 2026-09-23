import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_12_t_0_t_tail21 :
    instructionSequenceAt 250 false { bytes := artifactBytes, pos := 6926, limit := 7143 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[12]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 7075, limit := 7143 }) := by
  cbv

@[cbv_eval] theorem sequence_33_12_t_0_t_tail0 :
    instructionSequenceAt 271 false { bytes := artifactBytes, pos := 6885, limit := 7143 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7075, limit := 7143 }) := by
  cbv

@[cbv_eval] theorem sequence_33_12_t_tail0 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 6883, limit := 7143 } =
      .ok ((((((Cache.raw.codes[33]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7076, limit := 7143 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail12 :
    instructionSequenceAt 275 false { bytes := artifactBytes, pos := 6881, limit := 7143 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 12, .end), { bytes := artifactBytes, pos := 7143, limit := 7143 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail0 :
    instructionSequenceAt 287 false { bytes := artifactBytes, pos := 6856, limit := 7143 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7143, limit := 7143 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 6851, limit := 28315 } = .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 7143, limit := 28315 }) := by
  refine code_eq_of_parts (size := 290)
    (payload := { bytes := artifactBytes, pos := 6853, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 6856, limit := 7143 })
    (bodyFinish := { bytes := artifactBytes, pos := 7143, limit := 7143 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_33_tail0
  · rfl

#print axioms code33_decoded

end Project.Gpt2QuantizedCached.Artifact
