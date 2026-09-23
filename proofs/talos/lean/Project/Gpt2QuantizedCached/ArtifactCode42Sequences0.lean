import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_0_t_tail181 :
    instructionSequenceAt 1931 false { bytes := artifactBytes, pos := 12422, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 181, .end), { bytes := artifactBytes, pos := 12550, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_0_t_tail133 :
    instructionSequenceAt 1979 false { bytes := artifactBytes, pos := 12274, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 12550, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_0_t_tail85 :
    instructionSequenceAt 2027 false { bytes := artifactBytes, pos := 12146, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 12550, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_0_t_tail48 :
    instructionSequenceAt 2064 false { bytes := artifactBytes, pos := 12017, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 12550, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_12_t_0_t_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 11890, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12550, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_0_t_tail181 :
    instructionSequenceAt 1931 false { bytes := artifactBytes, pos := 13254, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 181, .end), { bytes := artifactBytes, pos := 13382, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_0_t_tail133 :
    instructionSequenceAt 1979 false { bytes := artifactBytes, pos := 13106, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 13382, limit := 13496 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_12_t_0_t_tail85 :
    instructionSequenceAt 2027 false { bytes := artifactBytes, pos := 12978, limit := 13496 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 13382, limit := 13496 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
