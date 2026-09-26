import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_88_e_tail98 :
    instructionSequenceAt 1038 false { bytes := artifactBytes, pos := 26873, limit := 27117 } =
      .ok ((((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true)[88]!).childBody true).drop 98, .end), { bytes := artifactBytes, pos := 27022, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_88_e_tail71 :
    instructionSequenceAt 1065 false { bytes := artifactBytes, pos := 26744, limit := 27117 } =
      .ok ((((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true)[88]!).childBody true).drop 71, .end), { bytes := artifactBytes, pos := 27022, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_88_e_tail7 :
    instructionSequenceAt 1129 false { bytes := artifactBytes, pos := 26615, limit := 27117 } =
      .ok ((((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true)[88]!).childBody true).drop 7, .end), { bytes := artifactBytes, pos := 27022, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_88_e_tail0 :
    instructionSequenceAt 1136 false { bytes := artifactBytes, pos := 26601, limit := 27117 } =
      .ok ((((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true)[88]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27022, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_tail88 :
    instructionSequenceAt 1138 false { bytes := artifactBytes, pos := 26532, limit := 27117 } =
      .ok ((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true).drop 88, .end), { bytes := artifactBytes, pos := 27061, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_tail29 :
    instructionSequenceAt 1197 false { bytes := artifactBytes, pos := 26403, limit := 27117 } =
      .ok ((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true).drop 29, .end), { bytes := artifactBytes, pos := 27061, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_61_e_tail0 :
    instructionSequenceAt 1226 false { bytes := artifactBytes, pos := 26329, limit := 27117 } =
      .ok ((((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true)[61]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27061, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_tail61 :
    instructionSequenceAt 1228 false { bytes := artifactBytes, pos := 26260, limit := 27117 } =
      .ok ((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true).drop 61, .end), { bytes := artifactBytes, pos := 27100, limit := 27117 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
