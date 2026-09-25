import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode59Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_tail2 :
    instructionSequenceAt 1287 false { bytes := artifactBytes, pos := 26131, limit := 27117 } =
      .ok ((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true).drop 2, .end), { bytes := artifactBytes, pos := 27100, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_tail0 :
    instructionSequenceAt 1289 false { bytes := artifactBytes, pos := 26127, limit := 27117 } =
      .ok ((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27100, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_tail34 :
    instructionSequenceAt 1291 false { bytes := artifactBytes, pos := 26096, limit := 27117 } =
      .ok ((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true).drop 34, .end), { bytes := artifactBytes, pos := 27101, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_tail0 :
    instructionSequenceAt 1325 false { bytes := artifactBytes, pos := 26001, limit := 27117 } =
      .ok ((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27101, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail12 :
    instructionSequenceAt 1327 false { bytes := artifactBytes, pos := 25970, limit := 27117 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 27102, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail3 :
    instructionSequenceAt 1336 false { bytes := artifactBytes, pos := 25841, limit := 27117 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 27102, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail0 :
    instructionSequenceAt 1339 false { bytes := artifactBytes, pos := 25834, limit := 27117 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27102, limit := 27117 }) := by
  cbv

@[cbv_eval] theorem sequence_59_tail21 :
    instructionSequenceAt 1341 false { bytes := artifactBytes, pos := 25803, limit := 27117 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 21, .end), { bytes := artifactBytes, pos := 27117, limit := 27117 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
