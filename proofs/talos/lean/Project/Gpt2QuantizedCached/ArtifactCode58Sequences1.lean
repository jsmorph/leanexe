import Project.Gpt2QuantizedCached.ArtifactCode58Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_tail42 :
    instructionSequenceAt 2087 true { bytes := artifactBytes, pos := 24111, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 42, .otherwise), { bytes := artifactBytes, pos := 24805, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_38_t_tail0 :
    instructionSequenceAt 2129 true { bytes := artifactBytes, pos := 24027, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false)[38]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 24805, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_46_t_0_t_tail23 :
    instructionSequenceAt 2050 false { bytes := artifactBytes, pos := 25441, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[107]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := artifactBytes, pos := 25576, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_107_e_46_t_0_t_tail0 :
    instructionSequenceAt 2073 false { bytes := artifactBytes, pos := 25392, limit := 26048 } =
      .ok ((((((((((Cache.raw.codes[58]!).body)[107]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25576, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_tail71 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 25008, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false).drop 71, .end), { bytes := artifactBytes, pos := 25146, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_tail55 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 24880, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false).drop 55, .end), { bytes := artifactBytes, pos := 25146, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_tail38 :
    instructionSequenceAt 2131 false { bytes := artifactBytes, pos := 24025, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false).drop 38, .end), { bytes := artifactBytes, pos := 25146, limit := 26048 }) := by
  cbv

@[cbv_eval] theorem sequence_58_59_t_0_t_tail0 :
    instructionSequenceAt 2169 false { bytes := artifactBytes, pos := 23941, limit := 26048 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[59]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25146, limit := 26048 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
