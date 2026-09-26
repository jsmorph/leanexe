import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode28Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_21_e_tail39 :
    instructionSequenceAt 912 false { bytes := artifactBytes, pos := 4935, limit := 5571 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 39, .end), { bytes := artifactBytes, pos := 5568, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_tail30 :
    instructionSequenceAt 921 false { bytes := artifactBytes, pos := 4780, limit := 5571 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 30, .end), { bytes := artifactBytes, pos := 5568, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_21_e_tail0 :
    instructionSequenceAt 951 false { bytes := artifactBytes, pos := 4652, limit := 5571 } =
      .ok ((((((Cache.raw.codes[28]!).body)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 5568, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail21 :
    instructionSequenceAt 953 false { bytes := artifactBytes, pos := 4645, limit := 5571 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 21, .end), { bytes := artifactBytes, pos := 5571, limit := 5571 }) := by
  cbv

@[cbv_eval] theorem sequence_28_tail0 :
    instructionSequenceAt 974 false { bytes := artifactBytes, pos := 4597, limit := 5571 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5571, limit := 5571 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
