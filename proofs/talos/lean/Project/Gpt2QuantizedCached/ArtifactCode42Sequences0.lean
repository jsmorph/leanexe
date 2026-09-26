import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_0_t_tail178 :
    instructionSequenceAt 1920 false { bytes := artifactBytes, pos := 12341, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 178, .end), { bytes := artifactBytes, pos := 12470, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_0_t_tail133 :
    instructionSequenceAt 1965 false { bytes := artifactBytes, pos := 12198, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 12470, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_0_t_tail85 :
    instructionSequenceAt 2013 false { bytes := artifactBytes, pos := 12070, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 12470, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_0_t_tail48 :
    instructionSequenceAt 2050 false { bytes := artifactBytes, pos := 11941, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 12470, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_0_t_tail0 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 11814, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12470, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_0_t_tail178 :
    instructionSequenceAt 1920 false { bytes := artifactBytes, pos := 13165, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 178, .end), { bytes := artifactBytes, pos := 13294, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_0_t_tail133 :
    instructionSequenceAt 1965 false { bytes := artifactBytes, pos := 13022, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 133, .end), { bytes := artifactBytes, pos := 13294, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_0_t_tail85 :
    instructionSequenceAt 2013 false { bytes := artifactBytes, pos := 12894, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := artifactBytes, pos := 13294, limit := 13408 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
