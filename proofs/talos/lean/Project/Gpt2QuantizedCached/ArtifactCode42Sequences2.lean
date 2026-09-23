import Project.Gpt2QuantizedCached.ArtifactCode42Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_tail0 :
    instructionSequenceAt 2128 false { bytes := artifactBytes, pos := 12694, limit := 13496 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 13394, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_0_t_tail18 :
    instructionSequenceAt 2144 false { bytes := artifactBytes, pos := 11525, limit := 13496 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[86]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 11653, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_0_t_tail0 :
    instructionSequenceAt 2162 false { bytes := artifactBytes, pos := 11494, limit := 13496 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[86]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11653, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_tail19 :
    instructionSequenceAt 2130 false { bytes := artifactBytes, pos := 11860, limit := 13496 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 13408, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_tail0 :
    instructionSequenceAt 2149 false { bytes := artifactBytes, pos := 11824, limit := 13496 } =
      .ok ((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13408, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_86_t_tail0 :
    instructionSequenceAt 2164 false { bytes := artifactBytes, pos := 11492, limit := 13496 } =
      .ok ((((((Cache.raw.codes[42]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11654, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_90_t_tail8 :
    instructionSequenceAt 2152 true { bytes := artifactBytes, pos := 11674, limit := 13496 } =
      .ok ((((((Cache.raw.codes[42]!).body)[90]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 11805, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_90_t_tail0 :
    instructionSequenceAt 2160 true { bytes := artifactBytes, pos := 11661, limit := 13496 } =
      .ok ((((((Cache.raw.codes[42]!).body)[90]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11805, limit := 13496 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
