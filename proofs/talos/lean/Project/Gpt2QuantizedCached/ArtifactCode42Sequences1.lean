import Project.Gpt2QuantizedCached.ArtifactCode42Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_0_t_tail48 :
    instructionSequenceAt 2064 false { bytes := artifactBytes, pos := 12849, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 13382, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_0_t_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 12722, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13382, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_tail0 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 11888, limit := 13496 } =
      .ok ((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12551, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_tail0 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 12720, limit := 13496 } =
      .ok ((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13383, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail21 :
    instructionSequenceAt 2107 true { bytes := artifactBytes, pos := 12565, limit := 13496 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 21, .otherwise), { bytes := artifactBytes, pos := 12694, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail12 :
    instructionSequenceAt 2116 true { bytes := artifactBytes, pos := 11886, limit := 13496 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 12694, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail0 :
    instructionSequenceAt 2128 true { bytes := artifactBytes, pos := 11862, limit := 13496 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12694, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_tail12 :
    instructionSequenceAt 2116 false { bytes := artifactBytes, pos := 12718, limit := 13496 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 13394, limit := 13496 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
