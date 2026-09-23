import Project.Gpt2QuantizedCached.ArtifactCode50Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_307_t_0_t_tail18 :
    instructionSequenceAt 3385 false { bytes := artifactBytes, pos := 18682, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[307]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18810, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_307_t_0_t_tail0 :
    instructionSequenceAt 3403 false { bytes := artifactBytes, pos := 18651, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[307]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18810, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_tail33 :
    instructionSequenceAt 3357 false { bytes := artifactBytes, pos := 19051, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false).drop 33, .end), { bytes := artifactBytes, pos := 19356, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_tail0 :
    instructionSequenceAt 3390 false { bytes := artifactBytes, pos := 18981, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19356, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_tail0 :
    instructionSequenceAt 3664 false { bytes := artifactBytes, pos := 15940, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[48]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16102, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_52_t_tail8 :
    instructionSequenceAt 3652 true { bytes := artifactBytes, pos := 16122, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[52]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16253, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_52_t_tail0 :
    instructionSequenceAt 3660 true { bytes := artifactBytes, pos := 16109, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16253, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_tail0 :
    instructionSequenceAt 3651 false { bytes := artifactBytes, pos := 16270, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[61]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16412, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
