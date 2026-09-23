import Project.Gpt2QuantizedCached.ArtifactCode50Sequences3
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_206_t_tail0 :
    instructionSequenceAt 3506 true { bytes := artifactBytes, pos := 17749, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[206]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17893, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_tail0 :
    instructionSequenceAt 3454 false { bytes := artifactBytes, pos := 18107, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[258]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18269, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_262_t_tail8 :
    instructionSequenceAt 3442 true { bytes := artifactBytes, pos := 18289, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[262]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18420, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_262_t_tail0 :
    instructionSequenceAt 3450 true { bytes := artifactBytes, pos := 18276, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[262]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18420, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_307_t_tail0 :
    instructionSequenceAt 3405 false { bytes := artifactBytes, pos := 18649, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[307]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18811, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_311_t_tail8 :
    instructionSequenceAt 3393 true { bytes := artifactBytes, pos := 18831, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[311]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18962, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_311_t_tail0 :
    instructionSequenceAt 3401 true { bytes := artifactBytes, pos := 18818, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[311]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18962, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_tail0 :
    instructionSequenceAt 3392 false { bytes := artifactBytes, pos := 18979, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[320]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19357, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
