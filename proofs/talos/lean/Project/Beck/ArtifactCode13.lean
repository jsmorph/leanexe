import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_13_16_t_0_t_tail82 :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 5427, limit := 5601 } =
      .ok ((((((((Cache.raw.codes[13]!).body)[16]!).childBody false)[0]!).childBody false).drop 82, .end), { bytes := artifactBytes, pos := 5562, limit := 5601 }) := by
  cbv

@[cbv_eval] theorem sequence_13_16_t_0_t_tail30 :
    instructionSequenceAt 353 false { bytes := artifactBytes, pos := 5299, limit := 5601 } =
      .ok ((((((((Cache.raw.codes[13]!).body)[16]!).childBody false)[0]!).childBody false).drop 30, .end), { bytes := artifactBytes, pos := 5562, limit := 5601 }) := by
  cbv

@[cbv_eval] theorem sequence_13_16_t_0_t_tail0 :
    instructionSequenceAt 383 false { bytes := artifactBytes, pos := 5234, limit := 5601 } =
      .ok ((((((((Cache.raw.codes[13]!).body)[16]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5562, limit := 5601 }) := by
  cbv

@[cbv_eval] theorem sequence_13_16_t_tail0 :
    instructionSequenceAt 385 false { bytes := artifactBytes, pos := 5232, limit := 5601 } =
      .ok ((((((Cache.raw.codes[13]!).body)[16]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5563, limit := 5601 }) := by
  cbv

@[cbv_eval] theorem sequence_13_tail16 :
    instructionSequenceAt 387 false { bytes := artifactBytes, pos := 5230, limit := 5601 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 16, .end), { bytes := artifactBytes, pos := 5601, limit := 5601 }) := by
  cbv

@[cbv_eval] theorem sequence_13_tail0 :
    instructionSequenceAt 403 false { bytes := artifactBytes, pos := 5198, limit := 5601 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5601, limit := 5601 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 5193, limit := 27068 } = .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 5601, limit := 27068 }) := by
  refine code_eq_of_parts (size := 406)
    (payload := { bytes := artifactBytes, pos := 5195, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5198, limit := 5601 })
    (bodyFinish := { bytes := artifactBytes, pos := 5601, limit := 5601 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_13_tail0
  · rfl

#print axioms code13_decoded

end Project.Beck.Artifact
