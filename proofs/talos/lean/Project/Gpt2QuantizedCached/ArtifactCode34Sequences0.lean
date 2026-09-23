import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_91_t_0_t_26_t_0_t_tail33 :
    instructionSequenceAt 1977 false { bytes := artifactBytes, pos := 8193, limit := 9283 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 33, .end), { bytes := artifactBytes, pos := 8321, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_26_t_0_t_tail0 :
    instructionSequenceAt 2010 false { bytes := artifactBytes, pos := 8103, limit := 9283 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8321, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_26_t_tail0 :
    instructionSequenceAt 2012 false { bytes := artifactBytes, pos := 8101, limit := 9283 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8322, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_0_t_tail18 :
    instructionSequenceAt 2084 false { bytes := artifactBytes, pos := 7263, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7391, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_0_t_tail0 :
    instructionSequenceAt 2102 false { bytes := artifactBytes, pos := 7232, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7391, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_0_t_tail18 :
    instructionSequenceAt 2035 false { bytes := artifactBytes, pos := 7749, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[78]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7877, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_0_t_tail0 :
    instructionSequenceAt 2053 false { bytes := artifactBytes, pos := 7718, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[78]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7877, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_tail26 :
    instructionSequenceAt 2014 false { bytes := artifactBytes, pos := 8099, limit := 9283 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false).drop 26, .end), { bytes := artifactBytes, pos := 8415, limit := 9283 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
