import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_99_t_0_t_tail23 :
    instructionSequenceAt 1843 false { bytes := artifactBytes, pos := 24142, limit := 25750 } =
      .ok ((((((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 24277, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_99_t_0_t_tail0 :
    instructionSequenceAt 1866 false { bytes := artifactBytes, pos := 24093, limit := 25750 } =
      .ok ((((((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24277, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_99_t_tail0 :
    instructionSequenceAt 1868 false { bytes := artifactBytes, pos := 24091, limit := 25750 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false)[99]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24278, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_103_t_tail14 :
    instructionSequenceAt 1850 true { bytes := artifactBytes, pos := 24316, limit := 25750 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false)[103]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 24445, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_103_t_tail0 :
    instructionSequenceAt 1864 true { bytes := artifactBytes, pos := 24286, limit := 25750 } =
      .ok ((((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false)[103]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24445, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_tail125 :
    instructionSequenceAt 1844 true { bytes := artifactBytes, pos := 24565, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 125, .otherwise), { bytes := artifactBytes, pos := 24694, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_tail103 :
    instructionSequenceAt 1866 true { bytes := artifactBytes, pos := 24284, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 103, .otherwise), { bytes := artifactBytes, pos := 24694, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_tail99 :
    instructionSequenceAt 1870 true { bytes := artifactBytes, pos := 24089, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 99, .otherwise), { bytes := artifactBytes, pos := 24694, limit := 25750 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
