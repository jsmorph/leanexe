import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences4

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail1621 :
    instructionSequenceAt 7219 false { bytes := artifactBytes, pos := 4281, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1621, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1565 :
    instructionSequenceAt 7275 false { bytes := artifactBytes, pos := 4149, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1565, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1509 :
    instructionSequenceAt 7331 false { bytes := artifactBytes, pos := 4016, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1509, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1453 :
    instructionSequenceAt 7387 false { bytes := artifactBytes, pos := 3882, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1453, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1397 :
    instructionSequenceAt 7443 false { bytes := artifactBytes, pos := 3749, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1397, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1341 :
    instructionSequenceAt 7499 false { bytes := artifactBytes, pos := 3617, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1341, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1285 :
    instructionSequenceAt 7555 false { bytes := artifactBytes, pos := 3485, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1285, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1229 :
    instructionSequenceAt 7611 false { bytes := artifactBytes, pos := 3352, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1229, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
