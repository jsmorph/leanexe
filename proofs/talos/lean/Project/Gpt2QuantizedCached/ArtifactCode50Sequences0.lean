import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_320_t_0_t_33_t_0_t_tail62 :
    instructionSequenceAt 3291 false { bytes := artifactBytes, pos := 19203, limit := 19510 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 62, .end), { bytes := artifactBytes, pos := 19331, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_33_t_0_t_tail10 :
    instructionSequenceAt 3343 false { bytes := artifactBytes, pos := 19074, limit := 19510 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 10, .end), { bytes := artifactBytes, pos := 19331, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_33_t_0_t_tail0 :
    instructionSequenceAt 3353 false { bytes := artifactBytes, pos := 19055, limit := 19510 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19331, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_33_t_tail0 :
    instructionSequenceAt 3355 false { bytes := artifactBytes, pos := 19053, limit := 19510 } =
      .ok ((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19332, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_0_t_tail18 :
    instructionSequenceAt 3644 false { bytes := artifactBytes, pos := 15973, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[48]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16101, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_0_t_tail0 :
    instructionSequenceAt 3662 false { bytes := artifactBytes, pos := 15942, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[48]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16101, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_0_t_tail6 :
    instructionSequenceAt 3643 false { bytes := artifactBytes, pos := 16282, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[61]!).childBody false)[0]!).childBody false).drop 6, .end), { bytes := artifactBytes, pos := 16411, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_0_t_tail0 :
    instructionSequenceAt 3649 false { bytes := artifactBytes, pos := 16272, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[61]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16411, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
