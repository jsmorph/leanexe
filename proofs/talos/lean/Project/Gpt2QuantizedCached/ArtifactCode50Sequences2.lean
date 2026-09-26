import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences1

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_307_t_0_t_tail18 :
    instructionSequenceAt 3377 false { bytes := artifactBytes, pos := 18554, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[307]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18682, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_307_t_0_t_tail0 :
    instructionSequenceAt 3395 false { bytes := artifactBytes, pos := 18523, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[307]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18682, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_tail31 :
    instructionSequenceAt 3351 false { bytes := artifactBytes, pos := 18919, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false).drop 31, .end), { bytes := artifactBytes, pos := 19220, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_320_t_0_t_tail0 :
    instructionSequenceAt 3382 false { bytes := artifactBytes, pos := 18853, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[320]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19220, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_48_t_tail0 :
    instructionSequenceAt 3656 false { bytes := artifactBytes, pos := 15812, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[48]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15974, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_52_t_tail8 :
    instructionSequenceAt 3644 true { bytes := artifactBytes, pos := 15994, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[52]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16125, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_52_t_tail0 :
    instructionSequenceAt 3652 true { bytes := artifactBytes, pos := 15981, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[52]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16125, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_61_t_tail0 :
    instructionSequenceAt 3643 false { bytes := artifactBytes, pos := 16142, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[61]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16284, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
