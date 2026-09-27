import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode24Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_8_t_0_t_tail37 :
    instructionSequenceAt 760 false { bytes := artifactBytes, pos := 8913, limit := 9622 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false).drop 37, .end), { bytes := artifactBytes, pos := 9605, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_tail0 :
    instructionSequenceAt 797 false { bytes := artifactBytes, pos := 8833, limit := 9622 } =
      .ok ((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9605, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_tail0 :
    instructionSequenceAt 799 false { bytes := artifactBytes, pos := 8831, limit := 9622 } =
      .ok ((((((Cache.raw.codes[24]!).body)[8]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9606, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail8 :
    instructionSequenceAt 801 false { bytes := artifactBytes, pos := 8829, limit := 9622 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 8, .end), { bytes := artifactBytes, pos := 9622, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail0 :
    instructionSequenceAt 809 false { bytes := artifactBytes, pos := 8813, limit := 9622 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 9622, limit := 9622 }) := by
  cbv


end Project.Beck.Artifact
