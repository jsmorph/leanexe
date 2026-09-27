import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences2

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail2517 :
    instructionSequenceAt 6323 false { bytes := artifactBytes, pos := 6415, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2517, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2461 :
    instructionSequenceAt 6379 false { bytes := artifactBytes, pos := 6282, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2461, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2405 :
    instructionSequenceAt 6435 false { bytes := artifactBytes, pos := 6148, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2405, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2349 :
    instructionSequenceAt 6491 false { bytes := artifactBytes, pos := 6014, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2349, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2293 :
    instructionSequenceAt 6547 false { bytes := artifactBytes, pos := 5881, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2293, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2237 :
    instructionSequenceAt 6603 false { bytes := artifactBytes, pos := 5749, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2237, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2181 :
    instructionSequenceAt 6659 false { bytes := artifactBytes, pos := 5615, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2181, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2125 :
    instructionSequenceAt 6715 false { bytes := artifactBytes, pos := 5481, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2125, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
