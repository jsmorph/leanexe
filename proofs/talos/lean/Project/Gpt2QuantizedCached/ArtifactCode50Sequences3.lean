import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_97_t_tail0 :
    instructionSequenceAt 3607 false { bytes := artifactBytes, pos := 16378, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[97]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16540, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_101_t_tail8 :
    instructionSequenceAt 3595 true { bytes := artifactBytes, pos := 16560, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[101]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16691, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_101_t_tail0 :
    instructionSequenceAt 3603 true { bytes := artifactBytes, pos := 16547, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[101]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16691, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_tail0 :
    instructionSequenceAt 3551 false { bytes := artifactBytes, pos := 16905, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[153]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17067, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_157_t_tail8 :
    instructionSequenceAt 3539 true { bytes := artifactBytes, pos := 17087, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[157]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17218, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_157_t_tail0 :
    instructionSequenceAt 3547 true { bytes := artifactBytes, pos := 17074, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[157]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17218, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_tail0 :
    instructionSequenceAt 3502 false { bytes := artifactBytes, pos := 17452, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[202]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17614, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_206_t_tail8 :
    instructionSequenceAt 3490 true { bytes := artifactBytes, pos := 17634, limit := 19374 } =
      .ok ((((((Cache.raw.codes[50]!).body)[206]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17765, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
