import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences6

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_50_tail61 :
    instructionSequenceAt 3645 false { bytes := artifactBytes, pos := 16140, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 61, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail52 :
    instructionSequenceAt 3654 false { bytes := artifactBytes, pos := 15979, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 52, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail48 :
    instructionSequenceAt 3658 false { bytes := artifactBytes, pos := 15810, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 48, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail7 :
    instructionSequenceAt 3699 false { bytes := artifactBytes, pos := 15681, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 7, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv

@[cbv_eval] theorem sequence_50_tail0 :
    instructionSequenceAt 3706 false { bytes := artifactBytes, pos := 15668, limit := 19374 } =
      .ok ((((Cache.raw.codes[50]!).body).drop 0, .end), { bytes := artifactBytes, pos := 19374, limit := 19374 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
