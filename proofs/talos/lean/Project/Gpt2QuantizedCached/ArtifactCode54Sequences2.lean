import Project.Gpt2QuantizedCached.ArtifactCode54Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_54_107_e_140_e_tail205 :
    instructionSequenceAt 2458 false { bytes := artifactBytes, pos := 22025, limit := 23753 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true).drop 205, .end), { bytes := artifactBytes, pos := 23610, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_tail150 :
    instructionSequenceAt 2513 false { bytes := artifactBytes, pos := 21896, limit := 23753 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true).drop 150, .end), { bytes := artifactBytes, pos := 23610, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_tail103 :
    instructionSequenceAt 2560 false { bytes := artifactBytes, pos := 21768, limit := 23753 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true).drop 103, .end), { bytes := artifactBytes, pos := 23610, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_tail43 :
    instructionSequenceAt 2620 false { bytes := artifactBytes, pos := 21639, limit := 23753 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true).drop 43, .end), { bytes := artifactBytes, pos := 23610, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_tail0 :
    instructionSequenceAt 2663 false { bytes := artifactBytes, pos := 21530, limit := 23753 } =
      .ok ((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23610, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_tail140 :
    instructionSequenceAt 2665 false { bytes := artifactBytes, pos := 21492, limit := 23753 } =
      .ok ((((((Cache.raw.codes[54]!).body)[107]!).childBody true).drop 140, .end), { bytes := artifactBytes, pos := 23691, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_tail79 :
    instructionSequenceAt 2726 false { bytes := artifactBytes, pos := 21363, limit := 23753 } =
      .ok ((((((Cache.raw.codes[54]!).body)[107]!).childBody true).drop 79, .end), { bytes := artifactBytes, pos := 23691, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_tail25 :
    instructionSequenceAt 2780 false { bytes := artifactBytes, pos := 21233, limit := 23753 } =
      .ok ((((((Cache.raw.codes[54]!).body)[107]!).childBody true).drop 25, .end), { bytes := artifactBytes, pos := 23691, limit := 23753 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
