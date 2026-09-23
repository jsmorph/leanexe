import Project.Gpt2QuantizedCached.ArtifactCode34Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_147_t_tail0 :
    instructionSequenceAt 1986 false { bytes := artifactBytes, pos := 8876, limit := 9283 } =
      .ok ((((((Cache.raw.codes[34]!).body)[147]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9208, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail147 :
    instructionSequenceAt 1988 false { bytes := artifactBytes, pos := 8874, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 147, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail138 :
    instructionSequenceAt 1997 false { bytes := artifactBytes, pos := 8713, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 138, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail134 :
    instructionSequenceAt 2001 false { bytes := artifactBytes, pos := 8544, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 134, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail92 :
    instructionSequenceAt 2043 false { bytes := artifactBytes, pos := 8416, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 92, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail91 :
    instructionSequenceAt 2044 false { bytes := artifactBytes, pos := 8044, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 91, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail82 :
    instructionSequenceAt 2053 false { bytes := artifactBytes, pos := 7883, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 82, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail78 :
    instructionSequenceAt 2057 false { bytes := artifactBytes, pos := 7714, limit := 9283 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 78, .end), { bytes := artifactBytes, pos := 9283, limit := 9283 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
