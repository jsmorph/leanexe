import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode34Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_91_t_0_t_tail0 :
    instructionSequenceAt 2032 false { bytes := artifactBytes, pos := 8000, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8359, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_0_t_tail18 :
    instructionSequenceAt 1971 false { bytes := artifactBytes, pos := 8523, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[134]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8651, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_0_t_tail0 :
    instructionSequenceAt 1989 false { bytes := artifactBytes, pos := 8492, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[134]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8651, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail97 :
    instructionSequenceAt 1879 false { bytes := artifactBytes, pos := 9022, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 97, .end), { bytes := artifactBytes, pos := 9151, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail39 :
    instructionSequenceAt 1937 false { bytes := artifactBytes, pos := 8894, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 9151, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail0 :
    instructionSequenceAt 1976 false { bytes := artifactBytes, pos := 8822, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9151, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_tail0 :
    instructionSequenceAt 2096 false { bytes := artifactBytes, pos := 7182, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7344, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_33_t_tail8 :
    instructionSequenceAt 2084 true { bytes := artifactBytes, pos := 7364, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7495, limit := 9227 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
