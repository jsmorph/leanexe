import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode25Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_21_e_122_t_tail8 :
    instructionSequenceAt 1133 true { bytes := artifactBytes, pos := 10493, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[122]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10624, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_122_t_tail0 :
    instructionSequenceAt 1141 true { bytes := artifactBytes, pos := 10480, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[122]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10624, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail175 :
    instructionSequenceAt 1090 false { bytes := artifactBytes, pos := 10773, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 175, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail134 :
    instructionSequenceAt 1131 false { bytes := artifactBytes, pos := 10645, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 134, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail122 :
    instructionSequenceAt 1143 false { bytes := artifactBytes, pos := 10478, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 122, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail118 :
    instructionSequenceAt 1147 false { bytes := artifactBytes, pos := 10309, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 118, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail59 :
    instructionSequenceAt 1206 false { bytes := artifactBytes, pos := 10149, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 59, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail46 :
    instructionSequenceAt 1219 false { bytes := artifactBytes, pos := 9980, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 46, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv


end Project.Beck.Artifact
