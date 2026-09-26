import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode58Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_tail38 :
    instructionSequenceAt 1931 true { bytes := artifactBytes, pos := 23961, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 38, .otherwise), { bytes := artifactBytes, pos := 24694, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_38_t_tail0 :
    instructionSequenceAt 1969 true { bytes := artifactBytes, pos := 23885, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 24694, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_46_t_0_t_tail20 :
    instructionSequenceAt 1893 false { bytes := artifactBytes, pos := 25233, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[105]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 20, .end), { bytes := artifactBytes, pos := 25362, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_46_t_0_t_tail0 :
    instructionSequenceAt 1913 false { bytes := artifactBytes, pos := 25194, limit := 25750 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[105]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25362, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_tail84 :
    instructionSequenceAt 1925 false { bytes := artifactBytes, pos := 24832, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false).drop 84, .end), { bytes := artifactBytes, pos := 24960, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_tail38 :
    instructionSequenceAt 1971 false { bytes := artifactBytes, pos := 23883, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false).drop 38, .end), { bytes := artifactBytes, pos := 24960, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_0_t_tail0 :
    instructionSequenceAt 2009 false { bytes := artifactBytes, pos := 23800, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[57]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24960, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_46_t_tail0 :
    instructionSequenceAt 1915 false { bytes := artifactBytes, pos := 25192, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[105]!).childBody true)[46]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25363, limit := 25750 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
