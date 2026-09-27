import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ExpArm.ArtifactCode0Sequences3

namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail2069 :
    instructionSequenceAt 6771 false { bytes := artifactBytes, pos := 5349, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2069, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail2013 :
    instructionSequenceAt 6827 false { bytes := artifactBytes, pos := 5216, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 2013, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1957 :
    instructionSequenceAt 6883 false { bytes := artifactBytes, pos := 5082, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1957, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1901 :
    instructionSequenceAt 6939 false { bytes := artifactBytes, pos := 4948, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1901, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1845 :
    instructionSequenceAt 6995 false { bytes := artifactBytes, pos := 4814, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1845, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1789 :
    instructionSequenceAt 7051 false { bytes := artifactBytes, pos := 4681, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1789, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1733 :
    instructionSequenceAt 7107 false { bytes := artifactBytes, pos := 4547, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1733, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv

@[cbv_eval] theorem sequence_0_tail1677 :
    instructionSequenceAt 7163 false { bytes := artifactBytes, pos := 4413, limit := 9057 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 1677, .end), { bytes := artifactBytes, pos := 9057, limit := 9057 }) := by
  cbv


end Project.ExpArm.Artifact
