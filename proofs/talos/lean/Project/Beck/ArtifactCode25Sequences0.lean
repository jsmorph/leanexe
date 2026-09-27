import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_21_e_42_t_0_t_tail18 :
    instructionSequenceAt 1201 false { bytes := artifactBytes, pos := 9846, limit := 10915 } =
      .ok ((((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[42]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 9974, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_42_t_0_t_tail0 :
    instructionSequenceAt 1219 false { bytes := artifactBytes, pos := 9815, limit := 10915 } =
      .ok ((((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[42]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9974, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_118_t_0_t_tail18 :
    instructionSequenceAt 1125 false { bytes := artifactBytes, pos := 10344, limit := 10915 } =
      .ok ((((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[118]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 10472, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_118_t_0_t_tail0 :
    instructionSequenceAt 1143 false { bytes := artifactBytes, pos := 10313, limit := 10915 } =
      .ok ((((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[118]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10472, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_42_t_tail0 :
    instructionSequenceAt 1221 false { bytes := artifactBytes, pos := 9813, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 9975, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_46_t_tail8 :
    instructionSequenceAt 1209 true { bytes := artifactBytes, pos := 9995, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[46]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 10126, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_46_t_tail0 :
    instructionSequenceAt 1217 true { bytes := artifactBytes, pos := 9982, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[46]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10126, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_118_t_tail0 :
    instructionSequenceAt 1145 false { bytes := artifactBytes, pos := 10311, limit := 10915 } =
      .ok ((((((((Cache.raw.codes[25]!).body)[21]!).childBody true)[118]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10473, limit := 10915 }) := by
  cbv


end Project.Beck.Artifact
