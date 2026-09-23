import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_12_t_0_t_tail39 :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 9401, limit := 9632 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[12]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 9542, limit := 9632 }) := by
  cbv

@[cbv_eval] theorem sequence_35_12_t_0_t_tail0 :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 9316, limit := 9632 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9542, limit := 9632 }) := by
  cbv

@[cbv_eval] theorem sequence_35_12_t_tail0 :
    instructionSequenceAt 330 false { bytes := artifactBytes, pos := 9314, limit := 9632 } =
      .ok ((((((Cache.raw.codes[35]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9543, limit := 9632 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail12 :
    instructionSequenceAt 332 false { bytes := artifactBytes, pos := 9312, limit := 9632 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 12, .end), { bytes := artifactBytes, pos := 9632, limit := 9632 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail0 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 9288, limit := 9632 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9632, limit := 9632 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 9283, limit := 28315 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 9632, limit := 28315 }) := by
  refine code_eq_of_parts (size := 347)
    (payload := { bytes := artifactBytes, pos := 9285, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 9288, limit := 9632 })
    (bodyFinish := { bytes := artifactBytes, pos := 9632, limit := 9632 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_35_tail0
  · rfl

#print axioms code35_decoded

end Project.Gpt2QuantizedCached.Artifact
