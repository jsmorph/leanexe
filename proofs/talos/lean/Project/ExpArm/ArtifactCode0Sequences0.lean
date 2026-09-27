import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_24_t_0_t_tail18 :
    instructionSequenceAt 8794 false { bytes := artifactBytes, pos := 299, limit := 9057 } =
      .ok ((((((((Cache.raw.codes[0]!).body)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 427, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_24_t_0_t_tail0 :
    instructionSequenceAt 8812 false { bytes := artifactBytes, pos := 268, limit := 9057 } =
      .ok ((((((((Cache.raw.codes[0]!).body)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 427, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_24_t_tail0 :
    instructionSequenceAt 8814 false { bytes := artifactBytes, pos := 266, limit := 9057 } =
      .ok ((((((Cache.raw.codes[0]!).body)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 428, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_28_t_tail8 :
    instructionSequenceAt 8802 true { bytes := artifactBytes, pos := 448, limit := 9057 } =
      .ok ((((((Cache.raw.codes[0]!).body)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 579, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_28_t_tail0 :
    instructionSequenceAt 8810 true { bytes := artifactBytes, pos := 435, limit := 9057 } =
      .ok ((((((Cache.raw.codes[0]!).body)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 579, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3573 :
    instructionSequenceAt 5267 false { bytes := artifactBytes, pos := 8928, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3573, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3520 :
    instructionSequenceAt 5320 false { bytes := artifactBytes, pos := 8800, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3520, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3467 :
    instructionSequenceAt 5373 false { bytes := artifactBytes, pos := 8671, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3467, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
