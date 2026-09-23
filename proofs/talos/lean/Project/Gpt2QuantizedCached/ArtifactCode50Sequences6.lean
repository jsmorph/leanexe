import Project.Gpt2QuantizedCached.ArtifactCode50Sequences5
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail206 :
    instructionSequenceAt 3508 false { bytes := artifactBytes, pos := 17747, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 206, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail202 :
    instructionSequenceAt 3512 false { bytes := artifactBytes, pos := 17578, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 202, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail166 :
    instructionSequenceAt 3548 false { bytes := artifactBytes, pos := 17361, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 166, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail157 :
    instructionSequenceAt 3557 false { bytes := artifactBytes, pos := 17200, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 157, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail153 :
    instructionSequenceAt 3561 false { bytes := artifactBytes, pos := 17031, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 153, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail110 :
    instructionSequenceAt 3604 false { bytes := artifactBytes, pos := 16834, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 110, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail101 :
    instructionSequenceAt 3613 false { bytes := artifactBytes, pos := 16673, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 101, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail97 :
    instructionSequenceAt 3617 false { bytes := artifactBytes, pos := 16504, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 97, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
