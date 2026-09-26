import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences3

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_206_t_tail0 :
    instructionSequenceAt 3498 true { bytes := artifactBytes, pos := 17621, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[206]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17765, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_tail0 :
    instructionSequenceAt 3446 false { bytes := artifactBytes, pos := 17979, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[258]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18141, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_262_t_tail8 :
    instructionSequenceAt 3434 true { bytes := artifactBytes, pos := 18161, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[262]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18292, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_262_t_tail0 :
    instructionSequenceAt 3442 true { bytes := artifactBytes, pos := 18148, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[262]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18292, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_307_t_tail0 :
    instructionSequenceAt 3397 false { bytes := artifactBytes, pos := 18521, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[307]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18683, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_311_t_tail8 :
    instructionSequenceAt 3385 true { bytes := artifactBytes, pos := 18703, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[311]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18834, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_311_t_tail0 :
    instructionSequenceAt 3393 true { bytes := artifactBytes, pos := 18690, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[311]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18834, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_tail0 :
    instructionSequenceAt 3384 false { bytes := artifactBytes, pos := 18851, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[320]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19221, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
