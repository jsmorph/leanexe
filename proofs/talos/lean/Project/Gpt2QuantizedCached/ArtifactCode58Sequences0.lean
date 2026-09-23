import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_99_t_0_t_tail23 :
    instructionSequenceAt 2003 false { bytes := artifactBytes, pos := 24292, limit := 26048 } =
      .ok ((((((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 24427, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_99_t_0_t_tail0 :
    instructionSequenceAt 2026 false { bytes := artifactBytes, pos := 24243, limit := 26048 } =
      .ok ((((((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24427, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_99_t_tail0 :
    instructionSequenceAt 2028 false { bytes := artifactBytes, pos := 24241, limit := 26048 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24428, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_103_t_tail14 :
    instructionSequenceAt 2010 true { bytes := artifactBytes, pos := 24466, limit := 26048 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false)[103]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 24595, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_103_t_tail0 :
    instructionSequenceAt 2024 true { bytes := artifactBytes, pos := 24436, limit := 26048 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false)[103]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24595, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_tail115 :
    instructionSequenceAt 2014 true { bytes := artifactBytes, pos := 24666, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 115, .otherwise), { bytes := artifactBytes, pos := 24805, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_tail103 :
    instructionSequenceAt 2026 true { bytes := artifactBytes, pos := 24434, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 103, .otherwise), { bytes := artifactBytes, pos := 24805, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_tail99 :
    instructionSequenceAt 2030 true { bytes := artifactBytes, pos := 24239, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 99, .otherwise), { bytes := artifactBytes, pos := 24805, limit := 26048 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
