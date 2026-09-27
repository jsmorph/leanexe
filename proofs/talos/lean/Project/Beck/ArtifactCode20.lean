import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_20_16_t_0_t_tail73 :
    instructionSequenceAt 358 false { bytes := artifactBytes, pos := 8005, limit := 8173 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[16]!).childBody false)[0]!).childBody false).drop 73, .end), { bytes := artifactBytes, pos := 8134, limit := 8173 }) := by
  cbv

@[cbv_eval] theorem sequence_20_16_t_0_t_tail36 :
    instructionSequenceAt 395 false { bytes := artifactBytes, pos := 7862, limit := 8173 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[16]!).childBody false)[0]!).childBody false).drop 36, .end), { bytes := artifactBytes, pos := 8134, limit := 8173 }) := by
  cbv

@[cbv_eval] theorem sequence_20_16_t_0_t_tail0 :
    instructionSequenceAt 431 false { bytes := artifactBytes, pos := 7758, limit := 8173 } =
      .ok ((((((((Cache.raw.codes[20]!).body)[16]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8134, limit := 8173 }) := by
  cbv

@[cbv_eval] theorem sequence_20_16_t_tail0 :
    instructionSequenceAt 433 false { bytes := artifactBytes, pos := 7756, limit := 8173 } =
      .ok ((((((Cache.raw.codes[20]!).body)[16]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8135, limit := 8173 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail16 :
    instructionSequenceAt 435 false { bytes := artifactBytes, pos := 7754, limit := 8173 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 16, .end), { bytes := artifactBytes, pos := 8173, limit := 8173 }) := by
  cbv

@[cbv_eval] theorem sequence_20_tail0 :
    instructionSequenceAt 451 false { bytes := artifactBytes, pos := 7722, limit := 8173 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8173, limit := 8173 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 7717, limit := 27068 } = .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 8173, limit := 27068 }) := by
  refine code_eq_of_parts (size := 454)
    (payload := { bytes := artifactBytes, pos := 7719, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 7722, limit := 8173 })
    (bodyFinish := { bytes := artifactBytes, pos := 8173, limit := 8173 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_20_tail0
  · rfl

#print axioms code20_decoded

end Project.Beck.Artifact
