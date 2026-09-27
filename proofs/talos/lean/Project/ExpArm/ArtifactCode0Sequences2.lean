import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences1

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail2965 :
    instructionSequenceAt 5875 false { bytes := artifactBytes, pos := 7480, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2965, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2909 :
    instructionSequenceAt 5931 false { bytes := artifactBytes, pos := 7347, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2909, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2853 :
    instructionSequenceAt 5987 false { bytes := artifactBytes, pos := 7214, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2853, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2797 :
    instructionSequenceAt 6043 false { bytes := artifactBytes, pos := 7080, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2797, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2741 :
    instructionSequenceAt 6099 false { bytes := artifactBytes, pos := 6946, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2741, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2685 :
    instructionSequenceAt 6155 false { bytes := artifactBytes, pos := 6813, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2685, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2629 :
    instructionSequenceAt 6211 false { bytes := artifactBytes, pos := 6681, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2629, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2573 :
    instructionSequenceAt 6267 false { bytes := artifactBytes, pos := 6548, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2573, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
