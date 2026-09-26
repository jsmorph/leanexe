import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_0_t_tail156 :
    instructionSequenceAt 738 false { bytes := artifactBytes, pos := 5388, limit := 5571 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 156, .end), { bytes := artifactBytes, pos := 5530, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_0_t_tail107 :
    instructionSequenceAt 787 false { bytes := artifactBytes, pos := 5254, limit := 5571 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 107, .end), { bytes := artifactBytes, pos := 5530, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_0_t_tail60 :
    instructionSequenceAt 834 false { bytes := artifactBytes, pos := 5125, limit := 5571 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 60, .end), { bytes := artifactBytes, pos := 5530, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_0_t_tail14 :
    instructionSequenceAt 880 false { bytes := artifactBytes, pos := 4997, limit := 5571 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 5530, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_0_t_tail0 :
    instructionSequenceAt 894 false { bytes := artifactBytes, pos := 4970, limit := 5571 } =
      .ok ((((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5530, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_12_t_tail0 :
    instructionSequenceAt 896 false { bytes := artifactBytes, pos := 4968, limit := 5571 } =
      .ok ((((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5531, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_tail12 :
    instructionSequenceAt 898 false { bytes := artifactBytes, pos := 4966, limit := 5571 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 5567, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_39_e_tail0 :
    instructionSequenceAt 910 false { bytes := artifactBytes, pos := 4942, limit := 5571 } =
      .ok ((((((((Cache.raw.codes[28]!).body)[21]!).childBody true)[39]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 5567, limit := 5571 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
