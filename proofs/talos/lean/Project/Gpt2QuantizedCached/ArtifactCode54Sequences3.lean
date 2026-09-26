import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode54Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_54_107_e_tail0 :
    instructionSequenceAt 2805 false { bytes := artifactBytes, pos := 21037, limit := 23617 } =
      .ok ((((((Cache.raw.codes[54]!).body)[107]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23555, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_tail107 :
    instructionSequenceAt 2807 false { bytes := artifactBytes, pos := 20999, limit := 23617 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 107, .end), { bytes := artifactBytes, pos := 23617, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_tail50 :
    instructionSequenceAt 2864 false { bytes := artifactBytes, pos := 20869, limit := 23617 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 50, .end), { bytes := artifactBytes, pos := 23617, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_tail9 :
    instructionSequenceAt 2905 false { bytes := artifactBytes, pos := 20724, limit := 23617 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 9, .end), { bytes := artifactBytes, pos := 23617, limit := 23617 }) := by
  cbv

@[cbv_eval] theorem sequence_54_tail0 :
    instructionSequenceAt 2914 false { bytes := artifactBytes, pos := 20703, limit := 23617 } =
      .ok ((((Cache.raw.codes[54]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23617, limit := 23617 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
