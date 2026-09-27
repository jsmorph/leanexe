import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences7

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail277 :
    instructionSequenceAt 8563 false { bytes := artifactBytes, pos := 1138, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 277, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail221 :
    instructionSequenceAt 8619 false { bytes := artifactBytes, pos := 1010, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 221, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail165 :
    instructionSequenceAt 8675 false { bytes := artifactBytes, pos := 881, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 165, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail109 :
    instructionSequenceAt 8731 false { bytes := artifactBytes, pos := 752, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 109, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail53 :
    instructionSequenceAt 8787 false { bytes := artifactBytes, pos := 623, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 53, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail28 :
    instructionSequenceAt 8812 false { bytes := artifactBytes, pos := 433, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 28, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail24 :
    instructionSequenceAt 8816 false { bytes := artifactBytes, pos := 264, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 24, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 8840 false { bytes := artifactBytes, pos := 217, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
