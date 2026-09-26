import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode42Sequences0

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_0_t_tail48 :
    instructionSequenceAt 2050 false { bytes := artifactBytes, pos := 12765, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 48, .end), { bytes := artifactBytes, pos := 13294, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_0_t_tail0 :
    instructionSequenceAt 2098 false { bytes := artifactBytes, pos := 12638, limit := 13408 } =
      .ok ((((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13294, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_10_t_tail0 :
    instructionSequenceAt 2100 false { bytes := artifactBytes, pos := 11812, limit := 13408 } =
      .ok ((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12471, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_10_t_tail0 :
    instructionSequenceAt 2100 false { bytes := artifactBytes, pos := 12636, limit := 13408 } =
      .ok ((((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 13295, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail19 :
    instructionSequenceAt 2093 true { bytes := artifactBytes, pos := 12485, limit := 13408 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 19, .otherwise), { bytes := artifactBytes, pos := 12614, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail10 :
    instructionSequenceAt 2102 true { bytes := artifactBytes, pos := 11810, limit := 13408 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 10, .otherwise), { bytes := artifactBytes, pos := 12614, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_t_tail0 :
    instructionSequenceAt 2112 true { bytes := artifactBytes, pos := 11790, limit := 13408 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12614, limit := 13408 }) := by
  cbv

@[cbv_eval] theorem sequence_42_99_t_0_t_19_e_tail10 :
    instructionSequenceAt 2102 false { bytes := artifactBytes, pos := 12634, limit := 13408 } =
      .ok ((((((((((Cache.raw.codes[42]!).body)[99]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 10, .end), { bytes := artifactBytes, pos := 13306, limit := 13408 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
