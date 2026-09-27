import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences5

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail1173 :
    instructionSequenceAt 7667 false { bytes := artifactBytes, pos := 3218, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1173, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1117 :
    instructionSequenceAt 7723 false { bytes := artifactBytes, pos := 3085, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1117, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1061 :
    instructionSequenceAt 7779 false { bytes := artifactBytes, pos := 2951, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1061, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1005 :
    instructionSequenceAt 7835 false { bytes := artifactBytes, pos := 2817, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1005, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail949 :
    instructionSequenceAt 7891 false { bytes := artifactBytes, pos := 2685, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 949, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail893 :
    instructionSequenceAt 7947 false { bytes := artifactBytes, pos := 2556, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 893, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail837 :
    instructionSequenceAt 8003 false { bytes := artifactBytes, pos := 2427, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 837, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail781 :
    instructionSequenceAt 8059 false { bytes := artifactBytes, pos := 2298, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 781, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
