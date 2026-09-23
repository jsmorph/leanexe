import Project.Gpt2QuantizedCached.ArtifactCode54Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail98 :
    instructionSequenceAt 2231 false { bytes := artifactBytes, pos := 22723, limit := 23753 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 98, .end), { bytes := artifactBytes, pos := 23400, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail53 :
    instructionSequenceAt 2276 false { bytes := artifactBytes, pos := 22594, limit := 23753 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 53, .end), { bytes := artifactBytes, pos := 23400, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail9 :
    instructionSequenceAt 2320 false { bytes := artifactBytes, pos := 22466, limit := 23753 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 9, .end), { bytes := artifactBytes, pos := 23400, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_125_e_tail0 :
    instructionSequenceAt 2329 false { bytes := artifactBytes, pos := 22442, limit := 23753 } =
      .ok ((((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true)[125]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23400, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_tail125 :
    instructionSequenceAt 2331 false { bytes := artifactBytes, pos := 22404, limit := 23753 } =
      .ok ((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true).drop 125, .end), { bytes := artifactBytes, pos := 23489, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_tail79 :
    instructionSequenceAt 2377 false { bytes := artifactBytes, pos := 22274, limit := 23753 } =
      .ok ((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true).drop 79, .end), { bytes := artifactBytes, pos := 23489, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_tail34 :
    instructionSequenceAt 2422 false { bytes := artifactBytes, pos := 22145, limit := 23753 } =
      .ok ((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true).drop 34, .end), { bytes := artifactBytes, pos := 23489, limit := 23753 }) := by
  cbv

@[cbv_eval] theorem sequence_54_107_e_140_e_205_e_tail0 :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 22063, limit := 23753 } =
      .ok ((((((((((Cache.raw.codes[54]!).body)[107]!).childBody true)[140]!).childBody true)[205]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23489, limit := 23753 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
