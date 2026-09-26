import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode34Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_147_t_tail0 :
    instructionSequenceAt 1978 false { bytes := artifactBytes, pos := 8820, limit := 9227 } =
      .ok ((((((Cache.raw.codes[34]!).body)[147]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9152, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail147 :
    instructionSequenceAt 1980 false { bytes := artifactBytes, pos := 8818, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 147, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail138 :
    instructionSequenceAt 1989 false { bytes := artifactBytes, pos := 8657, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 138, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail134 :
    instructionSequenceAt 1993 false { bytes := artifactBytes, pos := 8488, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 134, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail92 :
    instructionSequenceAt 2035 false { bytes := artifactBytes, pos := 8360, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 92, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail91 :
    instructionSequenceAt 2036 false { bytes := artifactBytes, pos := 7996, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 91, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail82 :
    instructionSequenceAt 2045 false { bytes := artifactBytes, pos := 7835, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 82, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail78 :
    instructionSequenceAt 2049 false { bytes := artifactBytes, pos := 7666, limit := 9227 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 78, .end), { bytes := artifactBytes, pos := 9227, limit := 9227 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
