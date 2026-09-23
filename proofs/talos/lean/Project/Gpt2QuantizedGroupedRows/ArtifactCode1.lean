import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_12_t_0_t_tail39 :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 519, limit := 750 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[12]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 660, limit := 750 }) := by
  cbv

@[cbv_eval] theorem sequence_1_12_t_0_t_tail0 :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 434, limit := 750 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 660, limit := 750 }) := by
  cbv

@[cbv_eval] theorem sequence_1_12_t_tail0 :
    instructionSequenceAt 330 false { bytes := artifactBytes, pos := 432, limit := 750 } =
      .ok ((((((Cache.raw.codes[1]!).body)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 661, limit := 750 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail12 :
    instructionSequenceAt 332 false { bytes := artifactBytes, pos := 430, limit := 750 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 12, .end), { bytes := artifactBytes, pos := 750, limit := 750 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 406, limit := 750 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 750, limit := 750 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 401, limit := 5441 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 750, limit := 5441 }) := by
  refine code_eq_of_parts (size := 347)
    (payload := { bytes := artifactBytes, pos := 403, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 406, limit := 750 })
    (bodyFinish := { bytes := artifactBytes, pos := 750, limit := 750 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
