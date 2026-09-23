import Project.Gpt2QuantizedCached.ArtifactCode59Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_tail2 :
    instructionSequenceAt 1287 false { bytes := artifactBytes, pos := 26429, limit := 27415 } =
      .ok ((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true).drop 2, .end), { bytes := artifactBytes, pos := 27398, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_34_e_tail0 :
    instructionSequenceAt 1289 false { bytes := artifactBytes, pos := 26425, limit := 27415 } =
      .ok ((((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true)[34]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27398, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_tail34 :
    instructionSequenceAt 1291 false { bytes := artifactBytes, pos := 26394, limit := 27415 } =
      .ok ((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true).drop 34, .end), { bytes := artifactBytes, pos := 27399, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_12_e_tail0 :
    instructionSequenceAt 1325 false { bytes := artifactBytes, pos := 26299, limit := 27415 } =
      .ok ((((((((Cache.raw.codes[59]!).body)[21]!).childBody true)[12]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27399, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail12 :
    instructionSequenceAt 1327 false { bytes := artifactBytes, pos := 26268, limit := 27415 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 12, .end), { bytes := artifactBytes, pos := 27400, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail3 :
    instructionSequenceAt 1336 false { bytes := artifactBytes, pos := 26139, limit := 27415 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 27400, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_21_e_tail0 :
    instructionSequenceAt 1339 false { bytes := artifactBytes, pos := 26132, limit := 27415 } =
      .ok ((((((Cache.raw.codes[59]!).body)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 27400, limit := 27415 }) := by
  cbv

@[cbv_eval] theorem sequence_59_tail21 :
    instructionSequenceAt 1341 false { bytes := artifactBytes, pos := 26101, limit := 27415 } =
      .ok ((((Cache.raw.codes[59]!).body).drop 21, .end), { bytes := artifactBytes, pos := 27415, limit := 27415 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
