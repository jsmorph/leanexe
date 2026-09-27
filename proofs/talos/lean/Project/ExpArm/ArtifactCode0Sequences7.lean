import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences6

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail725 :
    instructionSequenceAt 8115 false { bytes := artifactBytes, pos := 2170, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 725, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail669 :
    instructionSequenceAt 8171 false { bytes := artifactBytes, pos := 2042, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 669, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail613 :
    instructionSequenceAt 8227 false { bytes := artifactBytes, pos := 1913, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 613, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail557 :
    instructionSequenceAt 8283 false { bytes := artifactBytes, pos := 1784, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 557, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail501 :
    instructionSequenceAt 8339 false { bytes := artifactBytes, pos := 1655, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 501, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail445 :
    instructionSequenceAt 8395 false { bytes := artifactBytes, pos := 1526, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 445, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail389 :
    instructionSequenceAt 8451 false { bytes := artifactBytes, pos := 1396, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 389, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail333 :
    instructionSequenceAt 8507 false { bytes := artifactBytes, pos := 1266, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 333, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
