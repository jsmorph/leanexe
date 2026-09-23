import Project.Gpt2QuantizedCached.ArtifactCode58Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_107_e_46_t_tail0 :
    instructionSequenceAt 2075 false { bytes := artifactBytes, pos := 25390, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[107]!).childBody true)[46]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25577, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_50_t_tail14 :
    instructionSequenceAt 2057 true { bytes := artifactBytes, pos := 25615, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[107]!).childBody true)[50]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 25744, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_50_t_tail0 :
    instructionSequenceAt 2071 true { bytes := artifactBytes, pos := 25585, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[107]!).childBody true)[50]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25744, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_tail0 :
    instructionSequenceAt 2171 false { bytes := artifactBytes, pos := 23939, limit := 26048 } =
      .ok ((((((Cache.raw.codes[58]!).body)[59]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25147, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_tail56 :
    instructionSequenceAt 2067 false { bytes := artifactBytes, pos := 25754, limit := 26048 } =
      .ok ((((((Cache.raw.codes[58]!).body)[107]!).childBody true).drop 56, .end), { bytes := artifactBytes, pos := 25883, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_tail50 :
    instructionSequenceAt 2073 false { bytes := artifactBytes, pos := 25583, limit := 26048 } =
      .ok ((((((Cache.raw.codes[58]!).body)[107]!).childBody true).drop 50, .end), { bytes := artifactBytes, pos := 25883, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_tail46 :
    instructionSequenceAt 2077 false { bytes := artifactBytes, pos := 25388, limit := 26048 } =
      .ok ((((((Cache.raw.codes[58]!).body)[107]!).childBody true).drop 46, .end), { bytes := artifactBytes, pos := 25883, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_tail0 :
    instructionSequenceAt 2123 false { bytes := artifactBytes, pos := 25283, limit := 26048 } =
      .ok ((((((Cache.raw.codes[58]!).body)[107]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 25883, limit := 26048 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
