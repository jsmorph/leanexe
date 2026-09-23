import Project.Gpt2QuantizedCached.ArtifactCode34Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_33_t_tail0 :
    instructionSequenceAt 2100 true { bytes := artifactBytes, pos := 7399, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7543, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_tail0 :
    instructionSequenceAt 2055 false { bytes := artifactBytes, pos := 7716, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7878, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_82_t_tail8 :
    instructionSequenceAt 2043 true { bytes := artifactBytes, pos := 7898, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[82]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8029, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_82_t_tail0 :
    instructionSequenceAt 2051 true { bytes := artifactBytes, pos := 7885, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[82]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8029, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_tail0 :
    instructionSequenceAt 2042 false { bytes := artifactBytes, pos := 8046, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[91]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8416, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_134_t_tail0 :
    instructionSequenceAt 1999 false { bytes := artifactBytes, pos := 8546, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[134]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8708, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_138_t_tail8 :
    instructionSequenceAt 1987 true { bytes := artifactBytes, pos := 8728, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[138]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8859, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_138_t_tail0 :
    instructionSequenceAt 1995 true { bytes := artifactBytes, pos := 8715, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[138]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8859, limit := 9283 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
