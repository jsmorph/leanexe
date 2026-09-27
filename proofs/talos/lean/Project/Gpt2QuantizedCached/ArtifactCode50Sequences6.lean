import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences5

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail206 :
    instructionSequenceAt 3500 false { bytes := artifactBytes, pos := 17619, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 206, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail202 :
    instructionSequenceAt 3504 false { bytes := artifactBytes, pos := 17450, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 202, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail166 :
    instructionSequenceAt 3540 false { bytes := artifactBytes, pos := 17233, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 166, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail157 :
    instructionSequenceAt 3549 false { bytes := artifactBytes, pos := 17072, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 157, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail153 :
    instructionSequenceAt 3553 false { bytes := artifactBytes, pos := 16903, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 153, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail110 :
    instructionSequenceAt 3596 false { bytes := artifactBytes, pos := 16706, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 110, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail101 :
    instructionSequenceAt 3605 false { bytes := artifactBytes, pos := 16545, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 101, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail97 :
    instructionSequenceAt 3609 false { bytes := artifactBytes, pos := 16376, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 97, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
