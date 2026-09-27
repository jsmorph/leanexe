import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode42Sequences1

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 12614, limit := 13408 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 13306, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_0_t_tail18 :
    instructionSequenceAt 2128 false { bytes := artifactBytes, pos := 11453, limit := 13408 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[86]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 11581, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_0_t_tail0 :
    instructionSequenceAt 2146 false { bytes := artifactBytes, pos := 11422, limit := 13408 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[86]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11581, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_tail19 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 11788, limit := 13408 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 13320, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_tail0 :
    instructionSequenceAt 2133 false { bytes := artifactBytes, pos := 11752, limit := 13408 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13320, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_tail0 :
    instructionSequenceAt 2148 false { bytes := artifactBytes, pos := 11420, limit := 13408 } =
      .ok ((((((Cache.raw.codes[42]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11582, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_90_t_tail8 :
    instructionSequenceAt 2136 true { bytes := artifactBytes, pos := 11602, limit := 13408 } =
      .ok ((((((Cache.raw.codes[42]!).body)[90]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 11733, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_90_t_tail0 :
    instructionSequenceAt 2144 true { bytes := artifactBytes, pos := 11589, limit := 13408 } =
      .ok ((((((Cache.raw.codes[42]!).body)[90]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11733, limit := 13408 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
