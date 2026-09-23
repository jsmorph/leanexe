import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_29_t_0_t_tail18 :
    instructionSequenceAt 1100 false { bytes := artifactBytes, pos := 9855, limit := 10891 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[29]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 9983, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_29_t_0_t_tail0 :
    instructionSequenceAt 1118 false { bytes := artifactBytes, pos := 9824, limit := 10891 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[29]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9983, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_85_t_0_t_tail18 :
    instructionSequenceAt 1044 false { bytes := artifactBytes, pos := 10417, limit := 10891 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[85]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 10545, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_85_t_0_t_tail0 :
    instructionSequenceAt 1062 false { bytes := artifactBytes, pos := 10386, limit := 10891 } =
      .ok ((((((((Cache.raw.codes[37]!).body)[85]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10545, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_29_t_tail0 :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 9822, limit := 10891 } =
      .ok ((((((Cache.raw.codes[37]!).body)[29]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9984, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_33_t_tail8 :
    instructionSequenceAt 1108 true { bytes := artifactBytes, pos := 10004, limit := 10891 } =
      .ok ((((((Cache.raw.codes[37]!).body)[33]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10135, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_33_t_tail0 :
    instructionSequenceAt 1116 true { bytes := artifactBytes, pos := 9991, limit := 10891 } =
      .ok ((((((Cache.raw.codes[37]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10135, limit := 10891 }) := by
  cbv

@[cbv_eval] theorem sequence_37_85_t_tail0 :
    instructionSequenceAt 1064 false { bytes := artifactBytes, pos := 10384, limit := 10891 } =
      .ok ((((((Cache.raw.codes[37]!).body)[85]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10546, limit := 10891 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
