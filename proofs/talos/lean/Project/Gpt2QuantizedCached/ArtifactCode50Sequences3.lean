import Project.Gpt2QuantizedCached.ArtifactCode50Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_97_t_tail0 :
    instructionSequenceAt 3615 false { bytes := artifactBytes, pos := 16506, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[97]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16668, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_101_t_tail8 :
    instructionSequenceAt 3603 true { bytes := artifactBytes, pos := 16688, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[101]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16819, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_101_t_tail0 :
    instructionSequenceAt 3611 true { bytes := artifactBytes, pos := 16675, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[101]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16819, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_153_t_tail0 :
    instructionSequenceAt 3559 false { bytes := artifactBytes, pos := 17033, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[153]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17195, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_157_t_tail8 :
    instructionSequenceAt 3547 true { bytes := artifactBytes, pos := 17215, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[157]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17346, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_157_t_tail0 :
    instructionSequenceAt 3555 true { bytes := artifactBytes, pos := 17202, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[157]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17346, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_202_t_tail0 :
    instructionSequenceAt 3510 false { bytes := artifactBytes, pos := 17580, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[202]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17742, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_206_t_tail8 :
    instructionSequenceAt 3498 true { bytes := artifactBytes, pos := 17762, limit := 19510 } =
      .ok ((((((Cache.raw.codes[50]!).body)[206]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17893, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
