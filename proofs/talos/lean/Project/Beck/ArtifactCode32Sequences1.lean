import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode32Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_14_t_0_t_tail0 :
    instructionSequenceAt 716 false { bytes := artifactBytes, pos := 18820, limit := 19522 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19492, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_tail0 :
    instructionSequenceAt 718 false { bytes := artifactBytes, pos := 18818, limit := 19522 } =
      .ok ((((((Cache.raw.codes[32]!).body)[14]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19493, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail14 :
    instructionSequenceAt 720 false { bytes := artifactBytes, pos := 18816, limit := 19522 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 14, .end), { bytes := artifactBytes, pos := 19522, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_tail0 :
    instructionSequenceAt 734 false { bytes := artifactBytes, pos := 18788, limit := 19522 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19522, limit := 19522 }) := by
  cbv


end Project.Beck.Artifact
