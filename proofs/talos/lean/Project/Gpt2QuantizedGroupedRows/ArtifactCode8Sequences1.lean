import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode8Sequences0

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_0_t_tail48 :
    instructionSequenceAt 2048 false { bytes := artifactBytes, pos := 3939, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 4468, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_0_t_tail0 :
    instructionSequenceAt 2096 false { bytes := artifactBytes, pos := 3812, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4468, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_tail0 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 2986, limit := 4580 } =
      .ok ((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3645, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_tail0 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 3810, limit := 4580 } =
      .ok ((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4469, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail19 :
    instructionSequenceAt 2091 true { bytes := artifactBytes, pos := 3659, limit := 4580 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 19, .otherwise), { bytes := artifactBytes, pos := 3788, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail10 :
    instructionSequenceAt 2100 true { bytes := artifactBytes, pos := 2984, limit := 4580 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 3788, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_tail0 :
    instructionSequenceAt 2110 true { bytes := artifactBytes, pos := 2964, limit := 4580 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3788, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_tail10 :
    instructionSequenceAt 2100 false { bytes := artifactBytes, pos := 3808, limit := 4580 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 4480, limit := 4580 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
