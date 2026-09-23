import Project.Gpt2QuantizedCached.ArtifactCode34Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_91_t_0_t_tail0 :
    instructionSequenceAt 2040 false { bytes := artifactBytes, pos := 8048, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8415, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_0_t_tail18 :
    instructionSequenceAt 1979 false { bytes := artifactBytes, pos := 8579, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[134]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8707, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_0_t_tail0 :
    instructionSequenceAt 1997 false { bytes := artifactBytes, pos := 8548, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[134]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8707, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail97 :
    instructionSequenceAt 1887 false { bytes := artifactBytes, pos := 9078, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 97, .end), { bytes := artifactBytes, pos := 9207, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail39 :
    instructionSequenceAt 1945 false { bytes := artifactBytes, pos := 8950, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 39, .end), { bytes := artifactBytes, pos := 9207, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_147_t_0_t_tail0 :
    instructionSequenceAt 1984 false { bytes := artifactBytes, pos := 8878, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[147]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9207, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_tail0 :
    instructionSequenceAt 2104 false { bytes := artifactBytes, pos := 7230, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7392, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_33_t_tail8 :
    instructionSequenceAt 2092 true { bytes := artifactBytes, pos := 7412, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 7543, limit := 9283 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
