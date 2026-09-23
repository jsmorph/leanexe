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
    instructionSequenceAt 797 false { bytes := artifactBytes, pos := 5876, limit := 6531 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[57]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 6004, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_57_t_0_t_tail0 :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 5845, limit := 6531 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[57]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6004, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail81 :
    instructionSequenceAt 721 false { bytes := artifactBytes, pos := 6378, limit := 6531 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 81, .end), { bytes := artifactBytes, pos := 6507, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail29 :
    instructionSequenceAt 773 false { bytes := artifactBytes, pos := 6250, limit := 6531 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 29, .end), { bytes := artifactBytes, pos := 6507, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_0_t_tail0 :
    instructionSequenceAt 802 false { bytes := artifactBytes, pos := 6175, limit := 6531 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[70]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6507, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_57_t_tail0 :
    instructionSequenceAt 817 false { bytes := artifactBytes, pos := 5843, limit := 6531 } =
      .ok ((((((Cache.raw.codes[30]!).body)[57]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6005, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_61_t_tail8 :
    instructionSequenceAt 805 true { bytes := artifactBytes, pos := 6025, limit := 6531 } =
      .ok ((((((Cache.raw.codes[30]!).body)[61]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 6156, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_61_t_tail0 :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 6012, limit := 6531 } =
      .ok ((((((Cache.raw.codes[30]!).body)[61]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6156, limit := 6531 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
