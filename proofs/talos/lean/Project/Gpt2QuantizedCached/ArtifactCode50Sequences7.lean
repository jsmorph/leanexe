import Project.Gpt2QuantizedCached.ArtifactCode50Sequences6
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail61 :
    instructionSequenceAt 3653 false { bytes := artifactBytes, pos := 16268, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 61, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail52 :
    instructionSequenceAt 3662 false { bytes := artifactBytes, pos := 16107, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 52, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail48 :
    instructionSequenceAt 3666 false { bytes := artifactBytes, pos := 15938, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 48, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail7 :
    instructionSequenceAt 3707 false { bytes := artifactBytes, pos := 15809, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 7, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail0 :
    instructionSequenceAt 3714 false { bytes := artifactBytes, pos := 15796, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
