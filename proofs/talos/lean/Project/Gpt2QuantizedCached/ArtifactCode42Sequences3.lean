import Project.Gpt2QuantizedCached.ArtifactCode42Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_tail0 :
    instructionSequenceAt 2151 false { bytes := artifactBytes, pos := 11822, limit := 13496 } =
      .ok ((((((Cache.raw.codes[42]!).body)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13409, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail99 :
    instructionSequenceAt 2153 false { bytes := artifactBytes, pos := 11820, limit := 13496 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 99, .end), { bytes := artifactBytes, pos := 13496, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail90 :
    instructionSequenceAt 2162 false { bytes := artifactBytes, pos := 11659, limit := 13496 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 90, .end), { bytes := artifactBytes, pos := 13496, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail86 :
    instructionSequenceAt 2166 false { bytes := artifactBytes, pos := 11490, limit := 13496 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 86, .end), { bytes := artifactBytes, pos := 13496, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail43 :
    instructionSequenceAt 2209 false { bytes := artifactBytes, pos := 11361, limit := 13496 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 43, .end), { bytes := artifactBytes, pos := 13496, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_tail0 :
    instructionSequenceAt 2252 false { bytes := artifactBytes, pos := 11244, limit := 13496 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 13496, limit := 13496 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
