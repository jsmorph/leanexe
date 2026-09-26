import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_320_t_0_t_31_t_0_t_tail60 :
    instructionSequenceAt 3287 false { bytes := artifactBytes, pos := 19067, limit := 19374 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[31]!).childBody false)[0]!).childBody false).drop 60, .end), { bytes := artifactBytes, pos := 19195, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_31_t_0_t_tail8 :
    instructionSequenceAt 3339 false { bytes := artifactBytes, pos := 18938, limit := 19374 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[31]!).childBody false)[0]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 19195, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_31_t_0_t_tail0 :
    instructionSequenceAt 3347 false { bytes := artifactBytes, pos := 18923, limit := 19374 } =
      .ok ((((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[31]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19195, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_31_t_tail0 :
    instructionSequenceAt 3349 false { bytes := artifactBytes, pos := 18921, limit := 19374 } =
      .ok ((((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false)[31]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19196, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_0_t_tail18 :
    instructionSequenceAt 3636 false { bytes := artifactBytes, pos := 15845, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[48]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 15973, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_0_t_tail0 :
    instructionSequenceAt 3654 false { bytes := artifactBytes, pos := 15814, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[48]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15973, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_0_t_tail6 :
    instructionSequenceAt 3635 false { bytes := artifactBytes, pos := 16154, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[61]!).childBody false)[0]!).childBody false).drop 6, .end), { bytes := artifactBytes, pos := 16283, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_0_t_tail0 :
    instructionSequenceAt 3641 false { bytes := artifactBytes, pos := 16144, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[61]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16283, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
