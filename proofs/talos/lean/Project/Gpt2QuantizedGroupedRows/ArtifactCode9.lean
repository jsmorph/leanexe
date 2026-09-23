import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4689, limit := 4979 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4817, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4658, limit := 4979 } =
      .ok ((((((((Cache.raw.codes[9]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4817, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4656, limit := 4979 } =
      .ok ((((((Cache.raw.codes[9]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4818, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 4838, limit := 4979 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4969, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 4825, limit := 4979 } =
      .ok ((((((Cache.raw.codes[9]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4969, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4823, limit := 4979 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4979, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4654, limit := 4979 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 18, .end), { bytes := artifactBytes, pos := 4979, limit := 4979 }) := by
  cbv

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4617, limit := 4979 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4979, limit := 4979 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 4612, limit := 5441 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 4979, limit := 5441 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4614, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 4617, limit := 4979 })
    (bodyFinish := { bytes := artifactBytes, pos := 4979, limit := 4979 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
