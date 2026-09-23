import Project.Gpt2QuantizedCached.ArtifactCode50Sequences4
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail333 :
    instructionSequenceAt 3381 false { bytes := artifactBytes, pos := 19379, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 333, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail320 :
    instructionSequenceAt 3394 false { bytes := artifactBytes, pos := 18977, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 320, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail311 :
    instructionSequenceAt 3403 false { bytes := artifactBytes, pos := 18816, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 311, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail307 :
    instructionSequenceAt 3407 false { bytes := artifactBytes, pos := 18647, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 307, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail271 :
    instructionSequenceAt 3443 false { bytes := artifactBytes, pos := 18435, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 271, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail262 :
    instructionSequenceAt 3452 false { bytes := artifactBytes, pos := 18274, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 262, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail258 :
    instructionSequenceAt 3456 false { bytes := artifactBytes, pos := 18105, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 258, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail215 :
    instructionSequenceAt 3499 false { bytes := artifactBytes, pos := 17908, limit := 19510 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 215, .end), { bytes := artifactBytes, pos := 19510, limit := 19510 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
