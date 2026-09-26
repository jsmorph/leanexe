import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_57_t_0_t_tail18 :
    instructionSequenceAt 797 false { bytes := artifactBytes, pos := 5844, limit := 6499 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[57]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 5972, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_57_t_0_t_tail0 :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 5813, limit := 6499 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[57]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5972, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail81 :
    instructionSequenceAt 721 false { bytes := artifactBytes, pos := 6346, limit := 6499 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 81, .end), { bytes := artifactBytes, pos := 6475, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail29 :
    instructionSequenceAt 773 false { bytes := artifactBytes, pos := 6218, limit := 6499 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 6475, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail0 :
    instructionSequenceAt 802 false { bytes := artifactBytes, pos := 6143, limit := 6499 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6475, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_57_t_tail0 :
    instructionSequenceAt 817 false { bytes := artifactBytes, pos := 5811, limit := 6499 } =
      .ok ((((((Cache.raw.codes[30]!).body)[57]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5973, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_61_t_tail8 :
    instructionSequenceAt 805 true { bytes := artifactBytes, pos := 5993, limit := 6499 } =
      .ok ((((((Cache.raw.codes[30]!).body)[61]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 6124, limit := 6499 }) := by
  cbv

@[cbv_eval] theorem sequence_30_61_t_tail0 :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 5980, limit := 6499 } =
      .ok ((((((Cache.raw.codes[30]!).body)[61]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6124, limit := 6499 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
