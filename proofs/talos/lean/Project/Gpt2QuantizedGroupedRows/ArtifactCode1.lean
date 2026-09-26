import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_10_t_0_t_tail39 :
    instructionSequenceAt 283 false { bytes := artifactBytes, pos := 515, limit := 742 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[10]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 652, limit := 742 }) := by
  cbv

@[cbv_eval] theorem sequence_1_10_t_0_t_tail0 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 430, limit := 742 } =
      .ok ((((((((Cache.raw.codes[1]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 652, limit := 742 }) := by
  cbv

@[cbv_eval] theorem sequence_1_10_t_tail0 :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 428, limit := 742 } =
      .ok ((((((Cache.raw.codes[1]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 653, limit := 742 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail10 :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 426, limit := 742 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 10, .end), { bytes := artifactBytes, pos := 742, limit := 742 }) := by
  cbv

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 336 false { bytes := artifactBytes, pos := 406, limit := 742 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 742, limit := 742 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 401, limit := 5409 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 742, limit := 5409 }) := by
  refine code_eq_of_parts (size := 339)
    (payload := { bytes := artifactBytes, pos := 403, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 406, limit := 742 })
    (bodyFinish := { bytes := artifactBytes, pos := 742, limit := 742 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
