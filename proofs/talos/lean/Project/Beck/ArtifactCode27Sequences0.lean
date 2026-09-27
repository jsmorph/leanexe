import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_27_8_t_0_t_65_e_tail63 :
    instructionSequenceAt 506 false { bytes := artifactBytes, pos := 13307, limit := 13479 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false)[65]!).childBody true).drop 63, .end), { bytes := artifactBytes, pos := 13435, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_65_e_tail37 :
    instructionSequenceAt 532 false { bytes := artifactBytes, pos := 13172, limit := 13479 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false)[65]!).childBody true).drop 37, .end), { bytes := artifactBytes, pos := 13435, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_65_e_tail11 :
    instructionSequenceAt 558 false { bytes := artifactBytes, pos := 13044, limit := 13479 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false)[65]!).childBody true).drop 11, .end), { bytes := artifactBytes, pos := 13435, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_65_e_tail0 :
    instructionSequenceAt 569 false { bytes := artifactBytes, pos := 13022, limit := 13479 } =
      .ok ((((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false)[65]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 13435, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_tail65 :
    instructionSequenceAt 571 false { bytes := artifactBytes, pos := 12995, limit := 13479 } =
      .ok ((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false).drop 65, .end), { bytes := artifactBytes, pos := 13438, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_tail4 :
    instructionSequenceAt 632 false { bytes := artifactBytes, pos := 12857, limit := 13479 } =
      .ok ((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false).drop 4, .end), { bytes := artifactBytes, pos := 13438, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_0_t_tail0 :
    instructionSequenceAt 636 false { bytes := artifactBytes, pos := 12851, limit := 13479 } =
      .ok ((((((((Cache.raw.codes[27]!).body)[8]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13438, limit := 13479 }) := by
  cbv

@[cbv_eval] theorem sequence_27_8_t_tail0 :
    instructionSequenceAt 638 false { bytes := artifactBytes, pos := 12849, limit := 13479 } =
      .ok ((((((Cache.raw.codes[27]!).body)[8]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13439, limit := 13479 }) := by
  cbv


end Project.Beck.Artifact
