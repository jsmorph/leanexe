import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode8Sequences1

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_tail0 :
    instructionSequenceAt 2110 false { bytes := artifactBytes, pos := 3788, limit := 4580 } =
      .ok ((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 4480, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_0_t_tail18 :
    instructionSequenceAt 2126 false { bytes := artifactBytes, pos := 2627, limit := 4580 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[86]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2755, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_0_t_tail0 :
    instructionSequenceAt 2144 false { bytes := artifactBytes, pos := 2596, limit := 4580 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[86]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2755, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_tail19 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 2962, limit := 4580 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 4494, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_tail0 :
    instructionSequenceAt 2131 false { bytes := artifactBytes, pos := 2926, limit := 4580 } =
      .ok ((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4494, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_86_t_tail0 :
    instructionSequenceAt 2146 false { bytes := artifactBytes, pos := 2594, limit := 4580 } =
      .ok ((((((Cache.raw.codes[8]!).body)[86]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2756, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_90_t_tail8 :
    instructionSequenceAt 2134 true { bytes := artifactBytes, pos := 2776, limit := 4580 } =
      .ok ((((((Cache.raw.codes[8]!).body)[90]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2907, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_90_t_tail0 :
    instructionSequenceAt 2142 true { bytes := artifactBytes, pos := 2763, limit := 4580 } =
      .ok ((((((Cache.raw.codes[8]!).body)[90]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2907, limit := 4580 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
