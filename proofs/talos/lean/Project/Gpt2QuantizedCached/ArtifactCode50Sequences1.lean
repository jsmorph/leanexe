import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_97_t_0_t_tail18 :
    instructionSequenceAt 3587 false { bytes := artifactBytes, pos := 16411, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[97]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16539, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_97_t_0_t_tail0 :
    instructionSequenceAt 3605 false { bytes := artifactBytes, pos := 16380, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[97]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16539, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_0_t_tail18 :
    instructionSequenceAt 3531 false { bytes := artifactBytes, pos := 16938, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[153]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17066, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_0_t_tail0 :
    instructionSequenceAt 3549 false { bytes := artifactBytes, pos := 16907, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[153]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17066, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_0_t_tail18 :
    instructionSequenceAt 3482 false { bytes := artifactBytes, pos := 17485, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[202]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17613, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_0_t_tail0 :
    instructionSequenceAt 3500 false { bytes := artifactBytes, pos := 17454, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[202]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17613, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_0_t_tail18 :
    instructionSequenceAt 3426 false { bytes := artifactBytes, pos := 18012, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[258]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18140, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_0_t_tail0 :
    instructionSequenceAt 3444 false { bytes := artifactBytes, pos := 17981, limit := 19374 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[258]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18140, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
