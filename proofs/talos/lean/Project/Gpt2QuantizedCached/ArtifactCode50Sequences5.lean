import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences4

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail333 :
    instructionSequenceAt 3373 false { bytes := artifactBytes, pos := 19243, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 333, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail320 :
    instructionSequenceAt 3386 false { bytes := artifactBytes, pos := 18849, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 320, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail311 :
    instructionSequenceAt 3395 false { bytes := artifactBytes, pos := 18688, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 311, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail307 :
    instructionSequenceAt 3399 false { bytes := artifactBytes, pos := 18519, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 307, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail271 :
    instructionSequenceAt 3435 false { bytes := artifactBytes, pos := 18307, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 271, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail262 :
    instructionSequenceAt 3444 false { bytes := artifactBytes, pos := 18146, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 262, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail258 :
    instructionSequenceAt 3448 false { bytes := artifactBytes, pos := 17977, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 258, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail215 :
    instructionSequenceAt 3491 false { bytes := artifactBytes, pos := 17780, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 215, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
