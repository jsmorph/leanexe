import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_10_t_0_t_tail39 :
    instructionSequenceAt 283 false { bytes := artifactBytes, pos := 9341, limit := 9568 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[10]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 9478, limit := 9568 }) := by
  cbv

@[cbv_eval] theorem sequence_35_10_t_0_t_tail0 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 9256, limit := 9568 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9478, limit := 9568 }) := by
  cbv

@[cbv_eval] theorem sequence_35_10_t_tail0 :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 9254, limit := 9568 } =
      .ok ((((((Cache.raw.codes[35]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9479, limit := 9568 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail10 :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 9252, limit := 9568 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 10, .end), { bytes := artifactBytes, pos := 9568, limit := 9568 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail0 :
    instructionSequenceAt 336 false { bytes := artifactBytes, pos := 9232, limit := 9568 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9568, limit := 9568 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 9227, limit := 28017 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 9568, limit := 28017 }) := by
  refine code_eq_of_parts (size := 339)
    (payload := { bytes := artifactBytes, pos := 9229, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 9232, limit := 9568 })
    (bodyFinish := { bytes := artifactBytes, pos := 9568, limit := 9568 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_35_tail0
  · rfl

#print axioms code35_decoded

end Project.Gpt2QuantizedCached.Artifact
