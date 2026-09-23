import Project.Gpt2QuantizedCached.ArtifactCode50Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_97_t_0_t_tail18 :
    instructionSequenceAt 3595 false { bytes := artifactBytes, pos := 16539, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[97]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16667, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_97_t_0_t_tail0 :
    instructionSequenceAt 3613 false { bytes := artifactBytes, pos := 16508, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[97]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16667, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_0_t_tail18 :
    instructionSequenceAt 3539 false { bytes := artifactBytes, pos := 17066, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[153]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17194, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_0_t_tail0 :
    instructionSequenceAt 3557 false { bytes := artifactBytes, pos := 17035, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[153]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17194, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_0_t_tail18 :
    instructionSequenceAt 3490 false { bytes := artifactBytes, pos := 17613, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[202]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17741, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_0_t_tail0 :
    instructionSequenceAt 3508 false { bytes := artifactBytes, pos := 17582, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[202]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17741, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_0_t_tail18 :
    instructionSequenceAt 3434 false { bytes := artifactBytes, pos := 18140, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[258]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18268, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_258_t_0_t_tail0 :
    instructionSequenceAt 3452 false { bytes := artifactBytes, pos := 18109, limit := 19510 } =
      .ok ((((((((Cache.raw.codes[50]!).body)[258]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18268, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
