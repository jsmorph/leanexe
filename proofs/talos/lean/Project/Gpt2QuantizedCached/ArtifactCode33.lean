import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_10_t_0_t_tail21 :
    instructionSequenceAt 244 false { bytes := artifactBytes, pos := 6882, limit := 7095 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[10]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 7027, limit := 7095 }) := by
  cbv

@[cbv_eval] theorem sequence_33_10_t_0_t_tail0 :
    instructionSequenceAt 265 false { bytes := artifactBytes, pos := 6841, limit := 7095 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7027, limit := 7095 }) := by
  cbv

@[cbv_eval] theorem sequence_33_10_t_tail0 :
    instructionSequenceAt 267 false { bytes := artifactBytes, pos := 6839, limit := 7095 } =
      .ok ((((((Cache.raw.codes[33]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7028, limit := 7095 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail10 :
    instructionSequenceAt 269 false { bytes := artifactBytes, pos := 6837, limit := 7095 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 10, .end), { bytes := artifactBytes, pos := 7095, limit := 7095 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail0 :
    instructionSequenceAt 279 false { bytes := artifactBytes, pos := 6816, limit := 7095 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7095, limit := 7095 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 6811, limit := 28017 } = .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 7095, limit := 28017 }) := by
  refine code_eq_of_parts (size := 282)
    (payload := { bytes := artifactBytes, pos := 6813, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 6816, limit := 7095 })
    (bodyFinish := { bytes := artifactBytes, pos := 7095, limit := 7095 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_33_tail0
  · rfl

#print axioms code33_decoded

end Project.Gpt2QuantizedCached.Artifact
