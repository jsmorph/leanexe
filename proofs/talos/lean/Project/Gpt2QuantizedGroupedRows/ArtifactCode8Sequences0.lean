import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_0_t_tail178 :
    instructionSequenceAt 1918 false { bytes := artifactBytes, pos := 3515, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 178, .end), { bytes := artifactBytes, pos := 3644, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_0_t_tail133 :
    instructionSequenceAt 1963 false { bytes := artifactBytes, pos := 3372, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 3644, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_0_t_tail85 :
    instructionSequenceAt 2011 false { bytes := artifactBytes, pos := 3244, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 3644, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_0_t_tail48 :
    instructionSequenceAt 2048 false { bytes := artifactBytes, pos := 3115, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 3644, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_t_10_t_0_t_tail0 :
    instructionSequenceAt 2096 false { bytes := artifactBytes, pos := 2988, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3644, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_0_t_tail178 :
    instructionSequenceAt 1918 false { bytes := artifactBytes, pos := 4339, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 178, .end), { bytes := artifactBytes, pos := 4468, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_0_t_tail133 :
    instructionSequenceAt 1963 false { bytes := artifactBytes, pos := 4196, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 4468, limit := 4580 }) := by
  cbv

@[cbv_eval] theorem sequence_8_99_t_0_t_19_e_10_t_0_t_tail85 :
    instructionSequenceAt 2011 false { bytes := artifactBytes, pos := 4068, limit := 4580 } =
      .ok ((((((((((((((Cache.raw.codes[8]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 4468, limit := 4580 }) := by
  cbv


end Project.Gpt2QuantizedGroupedRows.Artifact
