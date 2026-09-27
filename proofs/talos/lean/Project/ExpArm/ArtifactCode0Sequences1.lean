import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences0

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail3413 :
    instructionSequenceAt 5427 false { bytes := artifactBytes, pos := 8543, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3413, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3357 :
    instructionSequenceAt 5483 false { bytes := artifactBytes, pos := 8410, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3357, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3301 :
    instructionSequenceAt 5539 false { bytes := artifactBytes, pos := 8277, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3301, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3245 :
    instructionSequenceAt 5595 false { bytes := artifactBytes, pos := 8144, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3245, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3189 :
    instructionSequenceAt 5651 false { bytes := artifactBytes, pos := 8011, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3189, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3133 :
    instructionSequenceAt 5707 false { bytes := artifactBytes, pos := 7878, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3133, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3077 :
    instructionSequenceAt 5763 false { bytes := artifactBytes, pos := 7744, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3077, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail3021 :
    instructionSequenceAt 5819 false { bytes := artifactBytes, pos := 7612, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 3021, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
