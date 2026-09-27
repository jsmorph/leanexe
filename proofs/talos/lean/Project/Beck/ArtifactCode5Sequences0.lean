import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_65_t_0_t_tail18 :
    instructionSequenceAt 1391 false { bytes := artifactBytes, pos := 2992, limit := 3678 } =
      .ok ((((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true)[65]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 3120, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_65_t_0_t_tail0 :
    instructionSequenceAt 1409 false { bytes := artifactBytes, pos := 2961, limit := 3678 } =
      .ok ((((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true)[65]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3120, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_40_t_0_t_tail18 :
    instructionSequenceAt 1496 false { bytes := artifactBytes, pos := 2413, limit := 3678 } =
      .ok ((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[40]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 2541, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_40_t_0_t_tail0 :
    instructionSequenceAt 1514 false { bytes := artifactBytes, pos := 2382, limit := 3678 } =
      .ok ((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[40]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2541, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_65_t_tail0 :
    instructionSequenceAt 1411 false { bytes := artifactBytes, pos := 2959, limit := 3678 } =
      .ok ((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true)[65]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3121, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_69_t_tail8 :
    instructionSequenceAt 1399 true { bytes := artifactBytes, pos := 3141, limit := 3678 } =
      .ok ((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true)[69]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 3272, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_69_t_tail0 :
    instructionSequenceAt 1407 true { bytes := artifactBytes, pos := 3128, limit := 3678 } =
      .ok ((((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true)[69]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 3272, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_40_t_tail0 :
    instructionSequenceAt 1516 false { bytes := artifactBytes, pos := 2380, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2542, limit := 3678 }) := by
  cbv


end Project.Beck.Artifact
