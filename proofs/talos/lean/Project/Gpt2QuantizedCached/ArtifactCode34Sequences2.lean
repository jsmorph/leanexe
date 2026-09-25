import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode34Sequences1

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_33_t_tail0 :
    instructionSequenceAt 2092 true { bytes := artifactBytes, pos := 7351, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7495, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_tail0 :
    instructionSequenceAt 2047 false { bytes := artifactBytes, pos := 7668, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7830, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_82_t_tail8 :
    instructionSequenceAt 2035 true { bytes := artifactBytes, pos := 7850, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[82]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7981, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_82_t_tail0 :
    instructionSequenceAt 2043 true { bytes := artifactBytes, pos := 7837, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7981, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_tail0 :
    instructionSequenceAt 2034 false { bytes := artifactBytes, pos := 7998, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[91]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8360, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_tail0 :
    instructionSequenceAt 1991 false { bytes := artifactBytes, pos := 8490, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[134]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8652, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_138_t_tail8 :
    instructionSequenceAt 1979 true { bytes := artifactBytes, pos := 8672, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[138]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8803, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_138_t_tail0 :
    instructionSequenceAt 1987 true { bytes := artifactBytes, pos := 8659, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[138]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8803, limit := 9227 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
