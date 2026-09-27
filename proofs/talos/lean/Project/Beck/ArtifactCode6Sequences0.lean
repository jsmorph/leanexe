import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_7_e_20_e_58_t_0_t_tail18 :
    instructionSequenceAt 1212 false { bytes := artifactBytes, pos := 4094, limit := 5006 } =
      .ok ((((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[58]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4222, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_58_t_0_t_tail0 :
    instructionSequenceAt 1230 false { bytes := artifactBytes, pos := 4063, limit := 5006 } =
      .ok ((((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[58]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4222, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_101_t_0_t_tail18 :
    instructionSequenceAt 1169 false { bytes := artifactBytes, pos := 4482, limit := 5006 } =
      .ok ((((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[101]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4610, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_101_t_0_t_tail0 :
    instructionSequenceAt 1187 false { bytes := artifactBytes, pos := 4451, limit := 5006 } =
      .ok ((((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[101]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4610, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_58_t_tail0 :
    instructionSequenceAt 1232 false { bytes := artifactBytes, pos := 4061, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[58]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4223, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_62_t_tail8 :
    instructionSequenceAt 1220 true { bytes := artifactBytes, pos := 4243, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[62]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4374, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_62_t_tail0 :
    instructionSequenceAt 1228 true { bytes := artifactBytes, pos := 4230, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[62]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4374, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_101_t_tail0 :
    instructionSequenceAt 1189 false { bytes := artifactBytes, pos := 4449, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[101]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4611, limit := 5006 }) := by
  cbv


end Project.Beck.Artifact
