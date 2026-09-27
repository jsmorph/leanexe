import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_69_t_tail16 :
    instructionSequenceAt 669 true { bytes := artifactBytes, pos := 9183, limit := 9622 } =
      .ok ((((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false)[69]!).childBody false).drop 16, .otherwise), { bytes := artifactBytes, pos := 9312, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_69_t_tail0 :
    instructionSequenceAt 685 true { bytes := artifactBytes, pos := 9151, limit := 9622 } =
      .ok ((((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 9312, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_tail109 :
    instructionSequenceAt 647 false { bytes := artifactBytes, pos := 9454, limit := 9622 } =
      .ok ((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false).drop 109, .end), { bytes := artifactBytes, pos := 9585, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_tail74 :
    instructionSequenceAt 682 false { bytes := artifactBytes, pos := 9325, limit := 9622 } =
      .ok ((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 9585, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_tail69 :
    instructionSequenceAt 687 false { bytes := artifactBytes, pos := 9149, limit := 9622 } =
      .ok ((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false).drop 69, .end), { bytes := artifactBytes, pos := 9585, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_tail32 :
    instructionSequenceAt 724 false { bytes := artifactBytes, pos := 9021, limit := 9622 } =
      .ok ((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false).drop 32, .end), { bytes := artifactBytes, pos := 9585, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_0_t_tail0 :
    instructionSequenceAt 756 false { bytes := artifactBytes, pos := 8917, limit := 9622 } =
      .ok ((((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9585, limit := 9622 }) := by
  cbv

@[cbv_eval] theorem sequence_24_8_t_0_t_37_t_tail0 :
    instructionSequenceAt 758 false { bytes := artifactBytes, pos := 8915, limit := 9622 } =
      .ok ((((((((((Cache.raw.codes[24]!).body)[8]!).childBody false)[0]!).childBody false)[37]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9586, limit := 9622 }) := by
  cbv


end Project.Beck.Artifact
