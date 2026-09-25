import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_51_36_t_0_t_tail18 :
    instructionSequenceAt 494 false { bytes := artifactBytes, pos := 19516, limit := 19931 } =
      .ok ((((((((Cache.raw.codes[51]!).body)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 19644, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_36_t_0_t_tail0 :
    instructionSequenceAt 512 false { bytes := artifactBytes, pos := 19485, limit := 19931 } =
      .ok ((((((((Cache.raw.codes[51]!).body)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19644, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_36_t_tail0 :
    instructionSequenceAt 514 false { bytes := artifactBytes, pos := 19483, limit := 19931 } =
      .ok ((((((Cache.raw.codes[51]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19645, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_40_t_tail8 :
    instructionSequenceAt 502 true { bytes := artifactBytes, pos := 19665, limit := 19931 } =
      .ok ((((((Cache.raw.codes[51]!).body)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 19796, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_40_t_tail0 :
    instructionSequenceAt 510 true { bytes := artifactBytes, pos := 19652, limit := 19931 } =
      .ok ((((((Cache.raw.codes[51]!).body)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19796, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_tail45 :
    instructionSequenceAt 507 false { bytes := artifactBytes, pos := 19803, limit := 19931 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 45, .end), { bytes := artifactBytes, pos := 19931, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_tail40 :
    instructionSequenceAt 512 false { bytes := artifactBytes, pos := 19650, limit := 19931 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 40, .end), { bytes := artifactBytes, pos := 19931, limit := 19931 }) := by
  cbv

@[cbv_eval] theorem sequence_51_tail36 :
    instructionSequenceAt 516 false { bytes := artifactBytes, pos := 19481, limit := 19931 } =
      .ok ((((Cache.raw.codes[51]!).body).drop 36, .end), { bytes := artifactBytes, pos := 19931, limit := 19931 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
