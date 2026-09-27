import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences8

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_tail195 :
    instructionSequenceAt 4519 false { bytes := artifactBytes, pos := 15313, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 195, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail156 :
    instructionSequenceAt 4558 false { bytes := artifactBytes, pos := 15094, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 156, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail152 :
    instructionSequenceAt 4562 false { bytes := artifactBytes, pos := 14925, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 152, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail113 :
    instructionSequenceAt 4601 false { bytes := artifactBytes, pos := 14706, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 113, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail109 :
    instructionSequenceAt 4605 false { bytes := artifactBytes, pos := 14537, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 109, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail70 :
    instructionSequenceAt 4644 false { bytes := artifactBytes, pos := 14318, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 70, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail66 :
    instructionSequenceAt 4648 false { bytes := artifactBytes, pos := 14149, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 66, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail1 :
    instructionSequenceAt 4713 false { bytes := artifactBytes, pos := 14021, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 1, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
