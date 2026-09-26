import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_91_t_0_t_24_t_0_t_tail31 :
    instructionSequenceAt 1973 false { bytes := artifactBytes, pos := 8132, limit := 9227 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 31, .end), { bytes := artifactBytes, pos := 8265, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_24_t_0_t_tail0 :
    instructionSequenceAt 2004 false { bytes := artifactBytes, pos := 8051, limit := 9227 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8265, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_24_t_tail0 :
    instructionSequenceAt 2006 false { bytes := artifactBytes, pos := 8049, limit := 9227 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8266, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_0_t_tail18 :
    instructionSequenceAt 2076 false { bytes := artifactBytes, pos := 7215, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7343, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_29_t_0_t_tail0 :
    instructionSequenceAt 2094 false { bytes := artifactBytes, pos := 7184, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7343, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_0_t_tail18 :
    instructionSequenceAt 2027 false { bytes := artifactBytes, pos := 7701, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[78]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 7829, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_78_t_0_t_tail0 :
    instructionSequenceAt 2045 false { bytes := artifactBytes, pos := 7670, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[78]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7829, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_91_t_0_t_tail24 :
    instructionSequenceAt 2008 false { bytes := artifactBytes, pos := 8047, limit := 9227 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[91]!).childBody false)[0]!).childBody false).drop 24, .end), { bytes := artifactBytes, pos := 8359, limit := 9227 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
