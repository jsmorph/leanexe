import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_27_3_e_16_t_0_t_tail13 :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 6833, limit := 7130 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[3]!).childBody true)[16]!).childBody false)[0]!).childBody false).drop 13, .end), { bytes := artifactBytes, pos := 6973, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_3_e_16_t_0_t_tail0 :
    instructionSequenceAt 352 false { bytes := artifactBytes, pos := 6805, limit := 7130 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[3]!).childBody true)[16]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6973, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_3_e_16_t_tail0 :
    instructionSequenceAt 354 false { bytes := artifactBytes, pos := 6803, limit := 7130 } =
      .ok ((((((((Cache.raw.codes[27]!).body)[3]!).childBody true)[16]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6974, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_3_e_tail29 :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 6998, limit := 7130 } =
      .ok ((((((Cache.raw.codes[27]!).body)[3]!).childBody true).drop 29, .end), { bytes := artifactBytes, pos := 7127, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_3_e_tail16 :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 6801, limit := 7130 } =
      .ok ((((((Cache.raw.codes[27]!).body)[3]!).childBody true).drop 16, .end), { bytes := artifactBytes, pos := 7127, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_3_e_tail0 :
    instructionSequenceAt 372 false { bytes := artifactBytes, pos := 6769, limit := 7130 } =
      .ok ((((((Cache.raw.codes[27]!).body)[3]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 7127, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail3 :
    instructionSequenceAt 374 false { bytes := artifactBytes, pos := 6762, limit := 7130 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 3, .end), { bytes := artifactBytes, pos := 7130, limit := 7130 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail0 :
    instructionSequenceAt 377 false { bytes := artifactBytes, pos := 6753, limit := 7130 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7130, limit := 7130 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 6748, limit := 19083 } = .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 7130, limit := 19083 }) := by
  refine code_eq_of_parts (size := 380)
    (payload := { bytes := artifactBytes, pos := 6750, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 6753, limit := 7130 })
    (bodyFinish := { bytes := artifactBytes, pos := 7130, limit := 7130 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_27_tail0
  · rfl

#print axioms code27_decoded

end Project.Gpt2CachedStep.Artifact
