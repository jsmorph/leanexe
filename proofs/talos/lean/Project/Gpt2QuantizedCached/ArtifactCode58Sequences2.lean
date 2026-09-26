import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode58Sequences1

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_58_105_e_50_t_tail14 :
    instructionSequenceAt 1897 true { bytes := artifactBytes, pos := 25400, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[105]!).childBody true)[50]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 25528, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_50_t_tail0 :
    instructionSequenceAt 1911 true { bytes := artifactBytes, pos := 25371, limit := 25750 } =
      .ok ((((((((Cache.raw.codes[58]!).body)[105]!).childBody true)[50]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25528, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_57_t_tail0 :
    instructionSequenceAt 2011 false { bytes := artifactBytes, pos := 23798, limit := 25750 } =
      .ok ((((((Cache.raw.codes[58]!).body)[57]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24961, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_tail50 :
    instructionSequenceAt 1913 false { bytes := artifactBytes, pos := 25369, limit := 25750 } =
      .ok ((((((Cache.raw.codes[58]!).body)[105]!).childBody true).drop 50, .end), { bytes := artifactBytes, pos := 25647, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_tail46 :
    instructionSequenceAt 1917 false { bytes := artifactBytes, pos := 25190, limit := 25750 } =
      .ok ((((((Cache.raw.codes[58]!).body)[105]!).childBody true).drop 46, .end), { bytes := artifactBytes, pos := 25647, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_105_e_tail0 :
    instructionSequenceAt 1963 false { bytes := artifactBytes, pos := 25097, limit := 25750 } =
      .ok ((((((Cache.raw.codes[58]!).body)[105]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 25647, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_tail105 :
    instructionSequenceAt 1965 false { bytes := artifactBytes, pos := 25066, limit := 25750 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 105, .end), { bytes := artifactBytes, pos := 25750, limit := 25750 }) := by
  cbv

@[cbv_eval] theorem sequence_58_tail57 :
    instructionSequenceAt 2013 false { bytes := artifactBytes, pos := 23796, limit := 25750 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 57, .end), { bytes := artifactBytes, pos := 25750, limit := 25750 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
